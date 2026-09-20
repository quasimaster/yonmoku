// ===== 立体四目並べ Web 版 エンジン API(モデル選択 + 読み手数スケジュール版)=====
// 設計: docs/設計書/Web公開/implementation-plan-model-select-and-custom-depth.md
//       調査: docs/設計書/Web公開/investigation-model-select-and-custom-depth.md
//
// 流用元 code/web/engine_api.cpp との差分は次の 4 点だけで、
// 盤面・棋譜・undo・評価値の正規化・状態遷移は完全に同一。
//   1. alpha を _w 版ヘッダ(engine_api_w.cpp と同じ経路)に載せ替える
//      ★非 _w 版 evaluate_alpha_inc_tbl.hpp は flag_tbl[256] が eval_weights.hpp と衝突するので
//        core と同居できない(調査 §2.1)。_w 版は旧実装とノード単位で一致することを実証済み
//        (docs/実行結果/benchmark-results-eval-weights-file.md §6)。
//   2. main_core2.cpp と同じヘッダ一式(tt2 / board_inc2 / ai_player_pvs_inc_id2 / evaluate_core2)を
//      同居させ、yon_set_model() で alpha / core を切り替える
//   3. 読み手数を「固定 4 バケット」から「最大 8 行のスケジュール表」に変える
//   4. 置換表は一律 22 bit(64 MB)。プロファイル毎の tt_bits は使わない
//
// ★core の重みは WASM からファイルを読めないので --embed-file で MEMFS に埋め込む(web/build.ps1)。
// ★CLI 側(code/*.hpp, code/main_*.cpp)には一切手を入れていない。
// ★-DEG_SELFCHECK=1 とは併用できない(g_eg_check_count が両 AI ヘッダで定義されるため)。

#ifndef USE_ASSERT
#define NDEBUG          // すべての #include より前(assert 無効化)
#endif

#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

// ★ ai_player_pvs_inc_id{,2}.hpp の YON_DEPTH_TARGET(turn, level) から呼ばれる。
//    マクロは前処理で展開されるだけなので、テンプレート定義より前に宣言が要る。
inline int yon_depth_target(int turn, int level);

#include "../common.hpp"
#include "../board.hpp"
#include "../player.hpp"
#include "../game.hpp"

// --- alpha: main_alpha_pvs_eval_inc_tbl_id_w.cpp と同じ経路 ---
#include "../tt.hpp"
#include "../board_inc.hpp"
#include "../ai_player_pvs_inc_id.hpp"
#include "../evaluate_alpha_inc_tbl_w.hpp"

// --- core: main_core2.cpp と同じ経路 ---
#include "../tt2.hpp"
#include "../board_inc2.hpp"
#include "../ai_player_pvs_inc_id2.hpp"
#include "../evaluate_core2.hpp"

#include <cmath>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif

using AIAlpha = AIPlayerPVSIncID<EvalFn>;
using AICore  = AIPlayerPVSIncID2<EvalFnCore2>;

// ===== モデル =====
// 1 モデル = (探索エンジン, 重みファイル) の組。重みは web/build.ps1 が --embed-file で
// MEMFS の /weights/... に埋め込む。新しい重みを足すときはこの表に 1 行足すだけでよい。
//   ★model 0 は組み込み既定値(ver7.2)で、公開中の Web 版と完全に同じ挙動になる。既定はこれ。
static const int ENGINE_ALPHA = 0;   // ai_player_pvs_inc_id  + evaluate_alpha_inc_tbl_w  (main_alpha_..._w 相当)
static const int ENGINE_CORE  = 1;   // ai_player_pvs_inc_id2 + evaluate_core2            (main_core2 相当)

struct ModelDef
{
	int         engine;
	const char* label;   // 重みファイルが読めなかったときの表示名
	const char* path;    // nullptr = 組み込み既定値
};

static const ModelDef MODELS[] = {
	{ ENGINE_ALPHA, "ver7.2",   nullptr                            },
	{ ENGINE_ALPHA, "ver8.1",   "/weights/alpha/ver8_1.txt"        },
	{ ENGINE_ALPHA, "ver8.2",   "/weights/alpha/ver8_2.txt"        },
	{ ENGINE_ALPHA, "ver8.2.5", "/weights/alpha/ver8_2_5.txt"      },
	{ ENGINE_CORE,  "ver1.0",   "/weights/core/ver1_0_core.txt"    },
};
static const int MODEL_NUM     = (int)(sizeof(MODELS) / sizeof(MODELS[0]));
static const int MODEL_DEFAULT = 0;

static const char* ENGINE_NAME[2] = { "alpha", "core" };

// ===== 難易度プロファイル(スケジュールの出発点として残す)=====
// 値は「読み手数 N」。内部の探索深さは d = N - 1。N は必ず偶数(評価関数の偶数手読み前提)。
// ID 3「標準」は現行 CLI と同一: 序盤 N=10 / 以降 10 / 12 / 26 → d = 9 / 9 / 11 / 25。
// ★置換表サイズは一律 TT_BITS になったので、流用元にあった tt_bits フィールドは持たない。
struct DifficultyProfile
{
	const char* name;
	int n_open;    // turn < 21
	int n_mid1;    // 21 <= turn < 29
	int n_mid2;    // 29 <= turn < 37
	int n_end;     // turn >= 37
};

static const DifficultyProfile PROFILES[] = {
	{ "\xe5\x85\xa5\xe9\x96\x80",                          4,  4,  6, 10 },  // 入門
	{ "\xe3\x82\x84\xe3\x81\x95\xe3\x81\x97\xe3\x81\x84",  6,  6,  8, 14 },  // やさしい
	{ "\xe3\x81\xb5\xe3\x81\xa4\xe3\x81\x86",              8,  8, 10, 20 },  // ふつう
	{ "\xe6\xa8\x99\xe6\xba\x96",                         10, 10, 12, 26 },  // 標準(既定 = 現行 CLI 相当)
	{ "\xe5\xbc\xb7\xe3\x81\x84",                         12, 12, 14, 26 },  // 強い
	{ "\xe6\x9c\x80\xe5\xbc\xb7",                         12, 14, 16, 26 },  // 最強
};
static const int PROFILE_NUM = (int)(sizeof(PROFILES) / sizeof(PROFILES[0]));
static const int PROFILE_DEFAULT = 3;

// プロファイルのバケット境界(スケジュールへ流し込むときの手数)
static const int PROFILE_TURNS[4] = { 1, 21, 29, 37 };

// ===== 読み手数スケジュール =====
static const int SCHED_MAX_ROWS = 8;    // 最大行数
static const int SCHED_MAX_PLY  = 30;   // 読み手数の上限(偶数)
static const int SCHED_MIN_PLY  = 2;    // 読み手数の下限(偶数)

static int g_sched_turn[SCHED_MAX_ROWS];   // この手数「以降」。昇順・先頭は必ず 1
static int g_sched_ply [SCHED_MAX_ROWS];   // 読み手数 N(偶数)
static int g_sched_len = 0;

// 置換表サイズ(一律 64 MB)
static const int TT_BITS = 22;

// ===== 内部状態(流用元 §3.2 と同じ)=====
static Board                     g_board;              // 現在局面(Me = 手番側)
static vector<pair<int, int> >   g_hand;               // ★棋譜。唯一の真実の源
static Game*                     g_dummy   = nullptr;  // AI が game->evaluates*_tmp[] を書くために必須
static AIAlpha*                  g_alpha   = nullptr;  // ★使っていないほうは必ず nullptr(TT 64MB を二重に持たない)
static AICore*                   g_core    = nullptr;
static Player*                   g_cur     = nullptr;  // g_alpha か g_core のどちらか
static int                       g_model   = MODEL_DEFAULT;
static bool                      g_human_is_black = true;
static int                       g_profile = PROFILE_DEFAULT;   // -1 = カスタム(表を直接編集した)
static bool                      g_eval_sec = false;   // いま evaluate_func に入っている sec(§2.4)
// 研究モードの解析セッション(詳細は「研究モード」節)。対局経路から参照するのでここで宣言する。
static bool                      g_ana_live     = false;   // 同じ局面の解析を継続中か
static bool                      g_ana_dirty_tt = false;   // 解析が置換表を汚したか(対局へ戻る前に捨てる)
static int                       g_status  = 0;        // 0=継続 1=黒勝ち 2=白勝ち 3=引分
static bool                      g_inited  = false;

// 直前の思考結果(yon_think / yon_analyze が更新)
static int       g_last_sq          = -1;
static int       g_last_score_black = 0;      // ★常に黒視点に正規化した評価値
static bool      g_last_valid       = false;
static bool      g_last_mate        = false;  // 即勝ち手を見つけた(探索を経ていない)
static double    g_last_ms          = 0.0;
static long long g_last_nodes       = 0;

// 勝ち確定を表す表示用スコア(シグモイドが 100% / 0% に振り切る大きさ)
static const int MATE_SCORE = 1000000;

// ===== 重み =====
// モデルごとに 1 つ持つ。version 1(alpha 用)も version 2(core 用)も EvalWeightsCore2 が読める
// (version 1 は core 項を 0 として読む)。読み込みは最初に必要になったときの 1 回だけ。
static EvalWeightsCore2 g_w[MODEL_NUM];
static unsigned char    g_w_state[MODEL_NUM];   // 0 = 未試行 / 1 = 読めた / 2 = 読めなかった

static const EvalWeightsCore2* model_weights(int i)
{
	if (i < 0 || i >= MODEL_NUM) return nullptr;
	if (g_w_state[i] == 0)
	{
		if (MODELS[i].path == nullptr)
		{
			g_w[i] = EvalWeightsCore2::builtin();
			g_w_state[i] = 1;
		}
		else
		{
			// WASM では MEMFS の絶対パス。native 検証ハーネス用に先頭の '/' を外した相対パスも試す
			// (EvalWeightsCore::load 自体も "" / "../" / "../../" の前置を試す)。
			string err;
			bool ok = g_w[i].load(MODELS[i].path, &err);
			if (!ok) ok = g_w[i].load(string(MODELS[i].path + 1), &err);
			g_w_state[i] = ok ? 1 : 2;
		}
	}
	return g_w_state[i] == 1 ? &g_w[i] : nullptr;
}

// alpha の評価関数に渡す重み。★model 0 は組み込み既定値そのものを使う(公開版と完全同一)
static const EvalWeights* alpha_weights(int i)
{
	if (MODELS[i].path == nullptr) return &EvalWeights::builtin();
	const EvalWeightsCore2* w = model_weights(i);
	return w ? &w->base : nullptr;
}

static inline const char* model_weights_name(int i)
{
	if (i < 0 || i >= MODEL_NUM) return "";
	const EvalWeightsCore2* w = model_weights(i);
	if (w && !w->base.name.empty()) return w->base.name.c_str();
	return MODELS[i].label;
}

static inline bool model_ok(int i)
{
	if (i < 0 || i >= MODEL_NUM) return false;
	return MODELS[i].engine == ENGINE_ALPHA ? alpha_weights(i) != nullptr
	                                        : model_weights(i) != nullptr;
}

// ===== 読み深さフック =====
// ai_player_pvs_inc_id{,2}.hpp の d_target がこれを呼ぶ。level は AI インスタンスの読み手数だが、
// 読み手数はスケジュール表から引くので使わない。
inline int yon_depth_target(int turn, int level)
{
	(void)level;
	if (g_sched_len <= 0) return 9;              // 保険(通常は yon_init() で必ず埋まる)
	int n = g_sched_ply[0];                      // 先頭行は必ず turn 1 から
	for (int i = 1; i < g_sched_len; i++)
	{
		if (turn >= g_sched_turn[i]) n = g_sched_ply[i];
		else break;                              // 昇順なのでここで打ち切れる
	}
	return n - 1;   // 総読み手数 N = d + 1
}

// ===== 補助 =====

// 絶対色のビットボード。Board::print() と同じ変換。
static inline void abs_bits(unsigned long long& black, unsigned long long& white)
{
	if (g_board.validate() == Color::Black) { black = g_board.Me; white = g_board.You; }
	else                                    { black = g_board.You; white = g_board.Me; }
}

// (x, y) に石を落としたときの z。満杯なら -1。
static inline int landing_z(int x, int y)
{
	if (x < 0 || x >= SIZE || y < 0 || y >= SIZE) return -1;
	for (int z = 0; z < SIZE; z++) if (g_board.get_cell(x, y, z) == Cell::None) return z;
	return -1;
}

// 置換表を空にする。new_search() の世代更新では不十分。
static inline void clear_tt()
{
	if (g_alpha)
	{
		for (TTEntry& e : g_alpha->tt.table) e.bound = TT_EMPTY;
		g_alpha->tt.generation = 0;
	}
	if (g_core)
	{
		for (unsigned long long i = 0; i <= g_core->tt.mask; i++) g_core->tt.table[i].bound = TT_EMPTY;
		g_core->tt.generation = 0;
	}
}

// 棋譜 g_hand から盤面を再生する。undo / 棋譜読込 / 局面ジャンプが共有する。
static void replay_from_hand()
{
	g_board = Board();
	g_status = 0;
	for (size_t i = 0; i < g_hand.size(); i++)
	{
		const enum State r = g_board.place(g_hand[i].first, g_hand[i].second);
		if (r == State::End)
		{
			// i 手目(0 始まり)を指した側の勝ち。偶数 index = 黒。
			g_status = (i % 2 == 0) ? 1 : 2;
			break;
		}
	}
	if (g_status == 0 && (int)g_hand.size() >= BOARD_SIZE) g_status = 3;
}

// スケジュール先頭行の N。AI::level に入れる(history のスケール用。読み深さには効かない)
static inline int sched_head_ply() { return g_sched_len > 0 ? g_sched_ply[0] : 10; }

// 現在のモデルの AI を用意する。モデルが変わるときだけ作り直す。
static void ensure_ai()
{
	if (!model_ok(g_model)) g_model = MODEL_DEFAULT;   // 重みが読めなければ既定モデルに落とす

	const bool need_alpha = (MODELS[g_model].engine == ENGINE_ALPHA);
	const bool have       = need_alpha ? (g_alpha != nullptr) : (g_core != nullptr);

	if (!have)
	{
		// ★片方だけを生かす(置換表 64 MB を二重に確保しない)
		delete g_dummy; g_dummy = nullptr;
		delete g_alpha; g_alpha = nullptr;
		delete g_core;  g_core  = nullptr;
		g_cur = nullptr;

		if (need_alpha)
		{
			g_alpha = new AIAlpha(sched_head_ply(), EvalFn{alpha_weights(g_model), false}, TT_BITS);
			g_cur = g_alpha;
		}
		else
		{
			g_core = new AICore(sched_head_ply(), EvalFnCore2{model_weights(g_model), false}, TT_BITS);
			g_cur = g_core;
		}
		g_dummy = new Game(g_cur, g_cur, false, {});   // Game ctor は set_verbose を呼ぶので非 nullptr が必須
	}
	else
	{
		clear_tt();
	}

	// AI が持つ色に応じた評価関数(先手用 / 後手用)。人間が黒なら AI は白(= sec)。
	if (g_alpha)
	{
		g_alpha->set_game(g_dummy);
		g_alpha->level = sched_head_ply();
		g_alpha->set_random(0);                      // MVP ではランダム手を使わない
		g_alpha->evaluate_func = EvalFn{alpha_weights(g_model), g_human_is_black};
	}
	else if (g_core)
	{
		g_core->set_game(g_dummy);
		g_core->level = sched_head_ply();
		g_core->set_random(0);
		g_core->evaluate_func = EvalFnCore2{model_weights(g_model), g_human_is_black};
	}
	g_eval_sec = g_human_is_black;   // ★研究モードの set_eval_side() と食い違わせない
}

// 評価関数の先後エントリ(EvalFn::sec)を差し替える。
//   false = 先手用 / true = 後手用。対局モードは「AI の色」で固定だが(= g_human_is_black)、
//   研究モードは任意手番の局面を解析するので「解析する局面の手番」に合わせる必要がある。
//   ★評価値の意味が変わるので、切り替えたら置換表は必ず捨てる。
static void set_eval_side(bool sec)
{
	if (sec == g_eval_sec) return;
	if (g_alpha) g_alpha->evaluate_func = EvalFn     {alpha_weights(g_model), sec};
	if (g_core)  g_core ->evaluate_func = EvalFnCore2{model_weights(g_model), sec};
	g_eval_sec = sec;
	clear_tt();
}

// スケジュールをプロファイルから流し込む(検証は不要。表の値は常に規則を満たす)
static void schedule_from_profile(int profile)
{
	if (profile < 0 || profile >= PROFILE_NUM) profile = PROFILE_DEFAULT;
	const DifficultyProfile& p = PROFILES[profile];
	const int n[4] = { p.n_open, p.n_mid1, p.n_mid2, p.n_end };
	for (int i = 0; i < 4; i++) { g_sched_turn[i] = PROFILE_TURNS[i]; g_sched_ply[i] = n[i]; }
	g_sched_len = 4;
	g_profile = profile;
}

// 探索して最善手と評価値を得る。**盤面は変更しない**(think / analyze 共通部)。
//   out_sq          : 着手マス 0..63
//   out_score_mover : 手番側から見た評価値
//   out_mate        : 即勝ち手を見つけた(探索を経ていないので評価値は無い)
static void search_only(int* out_sq, int* out_score_mover, bool* out_mate)
{
	// ★研究モードの解析は (1) 先後エントリを解析局面の手番に合わせ、(2) 置換表に
	//   対局の設定よりずっと深い結果を残す。どちらも対局へ持ち越すと挙動が変わるので、
	//   対局経路に入るところで必ず元へ戻す。研究モードを使わなければ何も起こらない(挙動不変)。
	set_eval_side(g_human_is_black);
	if (g_ana_dirty_tt) { clear_tt(); g_ana_dirty_tt = false; g_ana_live = false; }

	const int turn = g_board.turn();               // move() 内部と同じ値(石数 + 1)
	const bool black_to_move = (turn % 2 == 1);

	// move() は即勝ち手を見つけると評価値を書かずに return する。
	// 事前に番兵 INF を入れておき、書き換わったかどうかで判定する。
	int* slot = black_to_move ? &g_dummy->evaluatesfir_tmp[(turn + 1) / 2]
	                          : &g_dummy->evaluatessec_tmp[turn / 2];
	*slot = INF;

#ifdef BENCH
	g_node_count = 0;
#endif
	const auto st = chrono::steady_clock::now();
	const pair<int, int> xy = g_cur->move(g_board);   // Board は値渡しなので g_board は変わらない
	const auto el = chrono::steady_clock::now() - st;

	g_last_ms = chrono::duration_cast<chrono::microseconds>(el).count() / 1000.0;
#ifdef BENCH
	g_last_nodes = g_node_count;
#else
	g_last_nodes = -1;
#endif

	const int z = landing_z(xy.first, xy.second);
	*out_sq = IDX(xy.first, xy.second, z < 0 ? 0 : z);

	if (*slot == INF)   // 探索を経ずに即勝ち手を返した
	{
		*out_mate = true;
		*out_score_mover = MATE_SCORE;
	}
	else
	{
		*out_mate = false;
		*out_score_mover = *slot;
	}
}

// 手番側視点の評価値を黒視点に正規化する。
static inline int to_black_view(int score_mover)
{
	return (g_board.turn() % 2 == 1) ? score_mover : -score_mover;
}

// 実際に着手して状態を進める。
static enum State apply_move(int x, int y)
{
	const size_t idx = g_hand.size();
	const enum State r = g_board.place(x, y);
	if (r == State::Invalid) return r;
	g_hand.push_back(make_pair(x, y));
	if (r == State::End)          g_status = (idx % 2 == 0) ? 1 : 2;
	else if ((int)g_hand.size() >= BOARD_SIZE) g_status = 3;
	return r;
}

// ===== 研究モード(任意局面の反復深化解析 + 上位 K 手)=====
// 設計: docs/設計書/Web公開/implementation-plan-research-analysis.md
//
// 対局用の yon_think / search_only() は Player::move() を呼ぶので最善手 1 つしか得られない。
// 研究では上位 K 手の評価値が要るため、ここに専用の root ループを持つ。
//   ★CLI ヘッダは一切変更していない。evaluate_board / tt / killer / history はすべて public。
//   ★1 回の呼び出し = 1 つの深さ。JS 側の N = 8, 10, 12, … ループがそのまま反復深化の梯子になる
//     (同じ局面の続きなら root 順・killer/history・置換表を引き継ぐので梯子の登り直しが起きない)。

static const int ANA_MAX_K   = 5;
static const int ANA_MAX_PLY = 64;

static int       g_ana_ply        = 0;    // 直前に解析した読み手数 N
static int       g_ana_count      = 0;    // 候補手の件数
static int       g_ana_sq   [ANA_MAX_K];
static int       g_ana_score[ANA_MAX_K];  // ★黒視点に正規化済み
static int       g_ana_tied       = 0;    // 最下位と同値の可能性がある手の数
static int       g_ana_forced     = 0;    // 0 = 通常 / 1 = 即勝ち / 2 = 相手リーチ阻止のみ
static int       g_ana_complete   = 1;    // 1 = 完走 / 0 = 期限切れ
static double    g_ana_ms         = 0.0;
static long long g_ana_nodes      = 0;
static int       g_ana_root_moves = 0;

// 解析セッションの同一性。これが変わったら killer/history と root 順を作り直す。
static unsigned long long g_ana_key    = 0;
static int                g_ana_model  = -1;
static bool               g_ana_sec    = false;
static int                g_ana_last_d = -1;

// root 手の並び(前の深さのスコア降順)。次の深さの move ordering に使う。
static unsigned long long g_ana_order[16];
static int                g_ana_order_n = 0;

// 前の深さの K 位スコア(★手番側視点のまま)。次の深さのアスピレーション窓の下端に使う。
static int  g_ana_prev_k_score = 0;
static bool g_ana_prev_k_valid = false;

// root 手を move_order のグループ順に並べ直す(セッション開始時の初期順)
static void ana_order_reset(unsigned long long hand)
{
	g_ana_order_n = 0;
	for (const unsigned long long mask : move_order)
	{
		unsigned long long h = hand & mask;
		while (h)
		{
			const unsigned long long bit = h & -h;
			g_ana_order[g_ana_order_n++] = bit;
			h ^= bit;
		}
	}
}

template<typename AI>
static void ana_session_reset(AI* ai)
{
	memset(ai->killer, TT_NO_MOVE, sizeof(ai->killer));
	memset(ai->history, 0, sizeof(ai->history));
}

// root を 1 深さぶん探索し、上位 top_k 件を g_ana_* に書く(スコアは手番側視点のまま)。
//   戻り値 1 = 完走 / 0 = 期限切れで途中終了
//
// ★exact multi-PV: 親窓を (alphaK, INF) にする。beta = INF なので β カットが起こらず、
//   alphaK を上回った手の返り値は「厳密値」になる。K 位に届かない手は安い fail low で落ちる。
template<typename AI, typename BI>
static int ana_root_once(AI* ai, int d, int top_k, int deadline_ms,
                         const chrono::steady_clock::time_point& st)
{
	const BI bi = BI::from(g_board);
	const int n = g_ana_order_n;

	int sc[16];
	int t_sq[ANA_MAX_K], t_sc[ANA_MAX_K], tn = 0;
	int searched = 0;

	// アスピレーション: 前の深さの K 位スコアから窓の下端を先に立てる。
	// K 件そろうまで窓が (-INF, INF) のままだと K 回フルウィンドウ探索することになるので、
	// 最初から下端があるだけで大きく効く。高すぎて K 件そろわなければ下で必ず取り直す。
	const int ASP_MARGIN = 300;
	const int seed = (g_ana_prev_k_valid && g_ana_prev_k_score > -100000000
	                                     && g_ana_prev_k_score <  100000000)
	               ? g_ana_prev_k_score - ASP_MARGIN : -INF;

	int alphaK = seed;
	int base   = seed;      // K 件そろうまでの窓の下端
	bool retried = false;

	ai->tt.new_search();

 retry:
	for (int i = 0; i < n; i++)
	{
		const unsigned long long bit = g_ana_order[i];
		BI b = bi.place_fast_clone(bit);

		// K 件そろうまでは窓が (-INF, INF) なのでそのまま探索(厳密値が要る)。
		// そろったあとは null window で「K 位を上回るか」だけ先に調べ(scout)、
		// 上回ったときだけ開いた窓で厳密値を取り直す。★これが無いと K=3 で 2〜6 倍かかる。
		int ev;
		if (tn < top_k)
		{
			ev = -ai->evaluate_board(b, d, -INF, -alphaK, 0);
		}
		else
		{
			ev = -ai->evaluate_board(b, d, -alphaK - 1, -alphaK, 0);
			if (ev > alphaK) ev = -ai->evaluate_board(b, d, -INF, -alphaK, 0);
		}
		sc[i] = ev;
		searched++;

		if (ev > alphaK)   // ★窓の内側 = 厳密値
		{
			int p = (tn < top_k) ? tn : top_k - 1;   // あふれる場合は最下位を捨てる
			if (tn < top_k) tn++;
			while (p > 0 && t_sc[p - 1] < ev) { t_sc[p] = t_sc[p - 1]; t_sq[p] = t_sq[p - 1]; p--; }
			t_sc[p] = ev;
			t_sq[p] = __builtin_ctzll(bit);
			alphaK = (tn == top_k) ? t_sc[tn - 1] : base;   // K 件そろうまでは下端のまま
		}

		if (deadline_ms > 0 && i + 1 < n)
		{
			const long long el = chrono::duration_cast<chrono::milliseconds>(
				chrono::steady_clock::now() - st).count();
			if (el >= deadline_ms) break;
		}
	}

	// アスピレーションの下端が高すぎて K 件そろわなかった → 下端を外してやり直す
	if (!retried && seed != -INF && searched == n && tn < top_k && tn < n)
	{
		retried = true;
		tn = 0; searched = 0; alphaK = -INF; base = -INF;
		goto retry;
	}

	g_ana_count = tn;
	for (int i = 0; i < tn; i++) { g_ana_sq[i] = t_sq[i]; g_ana_score[i] = t_sc[i]; }

	// 次の深さのアスピレーション用(完走したときだけ信用する)
	g_ana_prev_k_valid = (searched == n && tn > 0);
	if (g_ana_prev_k_valid) g_ana_prev_k_score = t_sc[tn - 1];

	// 最下位と同値の可能性がある手(fail low の値は上界なので「可能性」止まり)
	g_ana_tied = 0;
	if (tn > 0)
	{
		for (int i = 0; i < searched; i++)
		{
			const int sq = __builtin_ctzll(g_ana_order[i]);
			bool listed = false;
			for (int k = 0; k < tn; k++) if (t_sq[k] == sq) { listed = true; break; }
			if (!listed && sc[i] >= t_sc[tn - 1]) g_ana_tied++;
		}
	}

	if (searched < n) return 0;   // 期限切れ。root 順は次の深さのために触らない

	// 次の深さのために root 順をスコア降順へ並べ替える(同点の相対順は維持 = 安定)
	for (int i = 1; i < n; i++)
	{
		const int               key_s = sc[i];
		const unsigned long long key_b = g_ana_order[i];
		int j = i - 1;
		while (j >= 0 && sc[j] < key_s) { sc[j + 1] = sc[j]; g_ana_order[j + 1] = g_ana_order[j]; j--; }
		sc[j + 1] = key_s;
		g_ana_order[j + 1] = key_b;
	}
	return 1;
}

// 現局面を N 手読みで 1 段だけ解析する。着手しない。
//   戻り値 1 = 完走 / 0 = 期限切れ / -1 = 解析不可 / -2 = 引数が不正
static int analyze_impl(int n, int top_k, int fresh_tt, int deadline_ms)
{
	if (n < 2 || n > ANA_MAX_PLY || (n % 2) != 0) return -2;
	if (top_k < 1 || top_k > ANA_MAX_K)           return -2;
	if (deadline_ms < 0)                          return -2;
	if (g_status != 0)                            return -1;

	unsigned long long hand = g_board.valid_move();
	if (!hand) return -1;

	// ★解析する局面の手番に評価関数の先後エントリを合わせる(対局モードは AI の色で固定)
	const bool sec = (g_board.turn() % 2 == 0);
	set_eval_side(sec);

	const int turn = g_board.turn();
	const int d    = n - 1;

	g_ana_ply      = n;
	g_ana_forced   = 0;
	g_ana_tied     = 0;
	g_ana_complete = 1;
	g_ana_ms       = 0.0;
	g_ana_nodes    = -1;
	g_ana_count    = 0;

	// --- 強制手(既存 move() と同じ規則: ai_player_pvs_inc_id.hpp:417-427)---
	{
		const unsigned long long r = hand & Board::reach(g_board.Me);
		if (r)   // 即勝ち。探索しない
		{
			g_ana_forced     = 1;
			g_ana_root_moves = __builtin_popcountll(r);
			unsigned long long h = r;
			while (h && g_ana_count < top_k)
			{
				const unsigned long long b = h & -h;
				g_ana_sq[g_ana_count]    = __builtin_ctzll(b);
				g_ana_score[g_ana_count] = to_black_view(INF - turn);
				g_ana_count++;
				h ^= b;
			}
			g_ana_tied   = g_ana_root_moves - g_ana_count;
			g_ana_ms     = 0.0;
			g_ana_nodes  = 0;              // 探索していない
			g_ana_live   = false;          // 探索していないので引き継ぐ状態が無い
			g_ana_last_d = -1;
			g_last_sq          = g_ana_sq[0];
			g_last_score_black = g_ana_score[0];
			g_last_mate        = true;
			g_last_valid       = true;
			g_last_ms          = 0.0;
			g_last_nodes       = 0;
			return 1;
		}
	}
	{
		const unsigned long long r = hand & Board::reach(g_board.You);
		if (r) { hand = r; g_ana_forced = 2; }   // 阻止手のみに絞る
	}
	g_ana_root_moves = __builtin_popcountll(hand);

	// --- セッションの継続判定 ---
	const unsigned long long key = TranspositionTable::hash(g_board);
	bool fresh = (fresh_tt != 0) || !g_ana_live || key != g_ana_key
	          || g_ana_model != g_model || g_ana_sec != sec;
	if (!fresh)
	{
		unsigned long long u = 0;
		for (int i = 0; i < g_ana_order_n; i++) u |= g_ana_order[i];
		if (u != hand) fresh = true;   // 保険(局面が同じなら起こらない)
	}

	if (fresh_tt) clear_tt();
	if (fresh)
	{
		ana_order_reset(hand);
		g_ana_prev_k_valid = false;
		if (g_alpha) ana_session_reset(g_alpha);
		if (g_core)  ana_session_reset(g_core);
	}

	// セッション開始時だけ d = 3, 5, … の梯子を登って TT と root 順を温める
	int d_start = fresh ? ((((d - 3) & 1) == 0) ? 3 : 4) : d;
	if (d_start > d) d_start = d;

	const auto st = chrono::steady_clock::now();
#ifdef BENCH
	g_node_count = 0;
#endif
	int complete = 1;
	for (int dd = d_start; dd <= d; dd += 2)
	{
		const int k = (dd == d) ? top_k : 1;   // 途中の深さは最善手だけでよい
		complete = (MODELS[g_model].engine == ENGINE_ALPHA)
		         ? ana_root_once<AIAlpha, BoardInc >(g_alpha, dd, k, deadline_ms, st)
		         : ana_root_once<AICore,  BoardInc2>(g_core,  dd, k, deadline_ms, st);
		if (!complete) break;
	}
	const auto el = chrono::steady_clock::now() - st;

	g_ana_ms = chrono::duration_cast<chrono::microseconds>(el).count() / 1000.0;
#ifdef BENCH
	g_ana_nodes = g_node_count;
#else
	g_ana_nodes = -1;
#endif
	g_ana_complete  = complete;
	g_ana_dirty_tt  = true;
	g_ana_live      = true;
	g_ana_key      = key;
	g_ana_model    = g_model;
	g_ana_sec      = sec;
	g_ana_last_d   = d;

	for (int i = 0; i < g_ana_count; i++) g_ana_score[i] = to_black_view(g_ana_score[i]);

	// HUD 互換のため既存の g_last_* も 1 位の値で更新する
	if (g_ana_count > 0)
	{
		g_last_sq          = g_ana_sq[0];
		g_last_score_black = g_ana_score[0];
		g_last_mate        = false;
		g_last_valid       = true;
		g_last_ms          = g_ana_ms;
		g_last_nodes       = g_ana_nodes;
	}
	return complete;
}

// ===== 公開 API =====
extern "C" {

// --- 状態を変える関数 ---

EMSCRIPTEN_KEEPALIVE void yon_init(void)
{
	if (g_inited) return;
	init_lines();
	init_sq_lines();
	init_eval_tbl2();               // ★flag_tbl + flag_tbl_sw。init_flag_tbl() を内包するので alpha 側もこれで足りる
	schedule_from_profile(PROFILE_DEFAULT);
	ensure_ai();
	g_inited = true;
}

// profile: 0..PROFILE_NUM-1 でプリセットを適用 / 負値なら現在のスケジュールを維持(カスタム)
EMSCRIPTEN_KEEPALIVE void yon_new_game(int human_is_black, int profile)
{
	yon_init();
	g_human_is_black = (human_is_black != 0);
	g_hand.clear();
	g_board = Board();
	g_status = 0;
	g_last_valid = false;
	g_last_sq = -1;
	g_last_score_black = 0;
	g_last_mate = false;
	g_last_ms = 0.0;
	g_last_nodes = 0;
	g_ana_live = false; g_ana_count = 0; g_ana_ply = 0;   // 研究モードの解析結果も捨てる
	if (profile >= 0) schedule_from_profile(profile);
	ensure_ai();
	clear_tt();                      // 設定が同じでも新規対局では必ずクリア
}

// 探索が使う乱数のシードを固定する(再現性が要るとき用。既定では誰も呼ばない)。
//   ★AI は「最善評価が並んだ手」をランダムに 1 つ選ぶ(ai_player_pvs_inc_id.hpp:587)。
//     乱数は common.hpp の グローバル `rng` 1 個で、対局をまたいでも巻き戻らない。
//     そのため同じ設定で 2 局目以降を回すと着手が変わる。同じ局を再現したいときはここで固定する。
EMSCRIPTEN_KEEPALIVE void yon_set_seed(unsigned int seed)
{
	yon_init();
	rng.seed(seed);
}

EMSCRIPTEN_KEEPALIVE void yon_set_profile(int profile)
{
	yon_init();
	schedule_from_profile(profile);
	ensure_ai();
	clear_tt();                      // 深い設定の表を浅い設定が再利用しないように
}

// model: MODELS[] の添字。戻り値 0 = OK / -1 = 範囲外 / -2 = 重みが読めない
EMSCRIPTEN_KEEPALIVE int yon_set_model(int model)
{
	yon_init();
	if (model < 0 || model >= MODEL_NUM) return -1;
	if (!model_ok(model)) return -2;
	if (model == g_model) { clear_tt(); return 0; }
	g_model = model;
	ensure_ai();
	clear_tt();                      // モデルが違えば評価値の意味が違うので必ずクリア
	return 0;
}

// スケジュールを設定する。turns / plies は len 個。
//   戻り値 0 = OK / -1 = 行数 / -2 = 先頭行が 1 でない / -3 = 手数が範囲外か昇順でない / -4 = 読み手数が不正
EMSCRIPTEN_KEEPALIVE int yon_set_schedule(const int* turns, const int* plies, int len)
{
	yon_init();
	if (!turns || !plies) return -1;
	if (len < 1 || len > SCHED_MAX_ROWS) return -1;
	if (turns[0] != 1) return -2;
	for (int i = 0; i < len; i++)
	{
		if (turns[i] < 1 || turns[i] > BOARD_SIZE) return -3;
		if (i > 0 && turns[i] <= turns[i - 1]) return -3;         // 厳密に昇順
		if (plies[i] < SCHED_MIN_PLY || plies[i] > SCHED_MAX_PLY) return -4;
		if (plies[i] % 2 != 0) return -4;                          // 偶数手読みの厳守
	}
	for (int i = 0; i < len; i++) { g_sched_turn[i] = turns[i]; g_sched_ply[i] = plies[i]; }
	g_sched_len = len;
	g_profile = -1;                  // 表を直接触ったらカスタム扱い
	ensure_ai();                     // level の付け替え
	clear_tt();
	return 0;
}

// 人間の着手。戻り値: 0=Continue / 1=End / 2=Invalid
EMSCRIPTEN_KEEPALIVE int yon_play(int x, int y)
{
	if (g_status != 0) return (int)State::Invalid;
	if (landing_z(x, y) < 0) return (int)State::Invalid;   // 事前に弾いて place() の cout を出さない
	return (int)apply_move(x, y);
}

// AI が思考して着手を確定する。戻り値: 着手マス 0..63 / エラー時 -1
EMSCRIPTEN_KEEPALIVE int yon_think(void)
{
	if (g_status != 0) return -1;
	if (!g_board.valid_move()) return -1;

	int sq = 0, score_mover = 0;
	bool mate = false;
	search_only(&sq, &score_mover, &mate);

	g_last_sq = sq;
	g_last_score_black = to_black_view(score_mover);   // ★ place() の前に評価する(手番が反転するため)
	g_last_mate = mate;
	g_last_valid = true;

	apply_move(X(sq), Y(sq));
	return sq;
}

// 現局面を探索するが着手はしない(棋譜解析用)
EMSCRIPTEN_KEEPALIVE int yon_analyze(void)
{
	if (g_status != 0) return -1;
	if (!g_board.valid_move()) return -1;

	int sq = 0, score_mover = 0;
	bool mate = false;
	search_only(&sq, &score_mover, &mate);

	g_last_sq = sq;
	g_last_score_black = to_black_view(score_mover);
	g_last_mate = mate;
	g_last_valid = true;
	return sq;
}

// --- 研究モード ---

// 現局面を「N 手読み」で 1 段だけ解析する。★着手しない・棋譜を変えない
//   n           : 読み手数(偶数、2 〜 64)
//   top_k       : 返してほしい候補手の数(1〜5)
//   fresh_tt    : 1 なら探索前に置換表をクリアする(厳密に N 手読みの値が欲しいとき)
//   deadline_ms : >0 なら root 手を 1 つ探索し終えるたびに経過時間を見て打ち切る(0 = 無制限)
//   戻り値      :  1 = 完走 / 0 = 期限切れで途中終了 / -1 = 解析不可 / -2 = 引数が不正
EMSCRIPTEN_KEEPALIVE int yon_analyze_ply(int n, int top_k, int fresh_tt, int deadline_ms)
{
	yon_init();
	return analyze_impl(n, top_k, fresh_tt, deadline_ms);
}

EMSCRIPTEN_KEEPALIVE int    yon_ana_ply(void)        { return g_ana_ply; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_count(void)      { return g_ana_count; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_sq(int i)        { return (i >= 0 && i < g_ana_count) ? g_ana_sq[i] : -1; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_score(int i)     { return (i >= 0 && i < g_ana_count) ? g_ana_score[i] : 0; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_tied(void)       { return g_ana_tied; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_forced(void)     { return g_ana_forced; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_complete(void)   { return g_ana_complete; }
EMSCRIPTEN_KEEPALIVE double yon_ana_ms(void)         { return g_ana_ms; }
EMSCRIPTEN_KEEPALIVE double yon_ana_nodes(void)      { return (double)g_ana_nodes; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_root_moves(void) { return g_ana_root_moves; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_max_k(void)      { return ANA_MAX_K; }
EMSCRIPTEN_KEEPALIVE int    yon_ana_max_ply(void)    { return ANA_MAX_PLY; }

// i 位の黒視点勝率 %(既存 yon_win_rate_black と同じシグモイド式)
EMSCRIPTEN_KEEPALIVE double yon_ana_winrate(int i)
{
	if (i < 0 || i >= g_ana_count) return 50.0;
	const double s = (double)g_ana_score[i];
	if (s >=  MATE_SCORE) return 100.0;
	if (s <= -MATE_SCORE) return 0.0;
	return 100.0 / (1.0 + exp(-s / 400.0));
}

// 【検証用】root の全手をフルウィンドウで探索し、厳密値を降順で書き出す。
//   out_sq / out_score は 16 要素ぶん確保しておくこと。戻り値は書いた件数。
//   ★枝刈りが一切効かないので遅い。yon_analyze_ply の上位 K が厳密であることの照合に使う。
EMSCRIPTEN_KEEPALIVE int yon_ana_full_scores(int n, int* out_sq, int* out_score)
{
	yon_init();
	if (n < 2 || n > ANA_MAX_PLY || (n % 2) != 0) return -2;
	if (g_status != 0 || !g_board.valid_move())   return -1;
	if (!out_sq || !out_score)                    return -2;

	set_eval_side(g_board.turn() % 2 == 0);
	clear_tt();

	unsigned long long hand = g_board.valid_move();
	{
		// ★即勝ちは探索しない。evaluate_board は「親の手で既に決着した局面」を扱えない
		//   (move() も root で先に return している: ai_player_pvs_inc_id.hpp:417-423)
		const unsigned long long r = hand & Board::reach(g_board.Me);
		if (r)
		{
			int m = 0;
			unsigned long long h = r;
			while (h) { const unsigned long long b = h & -h; out_sq[m] = __builtin_ctzll(b);
			            out_score[m] = to_black_view(INF - g_board.turn()); m++; h ^= b; }
			return m;
		}
		const unsigned long long y = hand & Board::reach(g_board.You);
		if (y) hand = y;
	}
	ana_order_reset(hand);

	const int d = n - 1;
	int sc[16], sq[16], m = 0;
	if (MODELS[g_model].engine == ENGINE_ALPHA)
	{
		ana_session_reset(g_alpha);
		g_alpha->tt.new_search();
		const BoardInc bi = BoardInc::from(g_board);
		for (int i = 0; i < g_ana_order_n; i++)
		{
			BoardInc b = bi.place_fast_clone(g_ana_order[i]);
			sc[m] = -g_alpha->evaluate_board(b, d, -INF, INF, 0);
			sq[m] = __builtin_ctzll(g_ana_order[i]);
			m++;
		}
	}
	else
	{
		ana_session_reset(g_core);
		g_core->tt.new_search();
		const BoardInc2 bi = BoardInc2::from(g_board);
		for (int i = 0; i < g_ana_order_n; i++)
		{
			BoardInc2 b = bi.place_fast_clone(g_ana_order[i]);
			sc[m] = -g_core->evaluate_board(b, d, -INF, INF, 0);
			sq[m] = __builtin_ctzll(g_ana_order[i]);
			m++;
		}
	}
	for (int i = 1; i < m; i++)   // 安定な降順挿入ソート
	{
		const int ks = sc[i], kq = sq[i];
		int j = i - 1;
		while (j >= 0 && sc[j] < ks) { sc[j + 1] = sc[j]; sq[j + 1] = sq[j]; j--; }
		sc[j + 1] = ks; sq[j + 1] = kq;
	}
	for (int i = 0; i < m; i++) { out_sq[i] = sq[i]; out_score[i] = to_black_view(sc[i]); }

	g_ana_live = false;   // 探索の作法が違うのでセッションは引き継がない
	return m;
}

// 1 手だけ巻き戻す(研究モード用)。戻り値: 巻き戻し後の手数
//   ★既存 yon_undo は「AI 手 + 人間手」の 2 手戻しなので研究には使えない
EMSCRIPTEN_KEEPALIVE int yon_undo_one(void)
{
	yon_init();
	if (g_hand.empty()) return 0;
	g_hand.pop_back();
	replay_from_hand();
	g_last_valid = false;
	g_ana_live   = false;      // 局面が変わったので解析セッションは切れる
	g_ana_count  = 0;
	g_ana_ply    = 0;
	return (int)g_hand.size();
}

// 「直前の AI 手 + 自分の手」を巻き戻す。戻り値: 巻き戻し後の手数
EMSCRIPTEN_KEEPALIVE int yon_undo(void)
{
	yon_init();
	// 人間の手の index パリティ: 黒番なら偶数、白番なら奇数
	const size_t human_parity = g_human_is_black ? 0 : 1;
	int j = (int)g_hand.size();
	while (j > 0 && (size_t)(j - 1) % 2 != human_parity) j--;   // 末尾の AI 手を読み飛ばす
	if (j == 0) return (int)g_hand.size();                      // 戻せる人間手が無い
	g_hand.resize(j - 1);
	replay_from_hand();
	g_last_valid = false;
	return (int)g_hand.size();
}

// 着手列(x, y の並び。len は要素数 = 手数 * 2)を読み込んで局面を再生する
EMSCRIPTEN_KEEPALIVE int yon_load(const int* xy, int len)
{
	yon_init();
	if (len < 0 || len % 2 != 0 || len > BOARD_SIZE * 2) return -1;
	g_hand.clear();
	g_board = Board();
	g_status = 0;
	for (int i = 0; i < len; i += 2)
	{
		if (landing_z(xy[i], xy[i + 1]) < 0) { replay_from_hand(); return -1; }
		if (apply_move(xy[i], xy[i + 1]) == State::Invalid) { replay_from_hand(); return -1; }
		if (g_status != 0) break;
	}
	g_last_valid = false;
	return (int)g_hand.size();
}

// --- 問い合わせるだけの関数(局面を変えない) ---

EMSCRIPTEN_KEEPALIVE unsigned long long yon_black(void)
{
	unsigned long long b, w; abs_bits(b, w); return b;
}
EMSCRIPTEN_KEEPALIVE unsigned long long yon_white(void)
{
	unsigned long long b, w; abs_bits(b, w); return w;
}

// 打てる列 (x, y) の 16bit マスク。bit (x + y*4)
EMSCRIPTEN_KEEPALIVE int yon_legal_columns(void)
{
	if (g_status != 0) return 0;
	int m = 0;
	for (int y = 0; y < SIZE; y++) for (int x = 0; x < SIZE; x++)
		if (landing_z(x, y) >= 0) m |= 1 << (x + y * SIZE);
	return m;
}

EMSCRIPTEN_KEEPALIVE int yon_landing_z(int x, int y) { return landing_z(x, y); }

EMSCRIPTEN_KEEPALIVE int yon_status(void) { return g_status; }
EMSCRIPTEN_KEEPALIVE int yon_turn(void)   { return g_board.turn(); }
EMSCRIPTEN_KEEPALIVE int yon_move_count(void) { return (int)g_hand.size(); }

// 次に指すのが黒か(1 = 黒番)
EMSCRIPTEN_KEEPALIVE int yon_black_to_move(void) { return g_board.turn() % 2 == 1 ? 1 : 0; }
EMSCRIPTEN_KEEPALIVE int yon_human_is_black(void) { return g_human_is_black ? 1 : 0; }

EMSCRIPTEN_KEEPALIVE int       yon_last_sq(void)     { return g_last_valid ? g_last_sq : -1; }
EMSCRIPTEN_KEEPALIVE int       yon_last_score(void)  { return g_last_score_black; }
EMSCRIPTEN_KEEPALIVE int       yon_last_is_mate(void){ return g_last_mate ? 1 : 0; }
EMSCRIPTEN_KEEPALIVE int       yon_last_valid(void)  { return g_last_valid ? 1 : 0; }
EMSCRIPTEN_KEEPALIVE double    yon_last_ms(void)     { return g_last_ms; }
EMSCRIPTEN_KEEPALIVE double    yon_last_nodes(void)  { return (double)g_last_nodes; }

// 黒視点の勝率 %(既存 verbose 出力と同じシグモイド式)
EMSCRIPTEN_KEEPALIVE double yon_win_rate_black(void)
{
	if (!g_last_valid) return 50.0;
	const double s = (double)g_last_score_black;
	if (s >=  MATE_SCORE) return 100.0;
	if (s <= -MATE_SCORE) return 0.0;
	return 100.0 / (1.0 + exp(-s / 400.0));
}

// 直前手のマス。無ければ -1
EMSCRIPTEN_KEEPALIVE int yon_last_played_sq(void)
{
	if (g_hand.empty()) return -1;
	const pair<int, int> xy = g_hand.back();
	// 再生済み盤面での高さを求める(その列の最上段の石)
	int z = -1;
	for (int k = 0; k < SIZE; k++) if (g_board.get_cell(xy.first, xy.second, k) != Cell::None) z = k;
	if (z < 0) return -1;
	return IDX(xy.first, xy.second, z);
}

// 勝利した 4 石のビット。勝敗が付いていなければ 0
EMSCRIPTEN_KEEPALIVE unsigned long long yon_win_line(void)
{
	if (g_status != 1 && g_status != 2) return 0uLL;
	unsigned long long b, w; abs_bits(b, w);
	const unsigned long long win = (g_status == 1) ? b : w;
	for (int i = 0; i < LINES_NUM; i++)
		if ((win & LINES[i]) == LINES[i]) return LINES[i];
	return 0uLL;
}

// color: 1 = 黒 / 2 = 白。リーチ(次に置けば四目)のマスのうち、実際に着手可能なもの
EMSCRIPTEN_KEEPALIVE unsigned long long yon_reach(int color)
{
	unsigned long long b, w; abs_bits(b, w);
	const unsigned long long r = Board::reach(color == 1 ? b : w);
	return r & g_board.valid_move();
}

// 棋譜を書き出す。out には手数 * 2 個の int が入る。戻り値は手数
EMSCRIPTEN_KEEPALIVE int yon_hand(int* out)
{
	for (size_t i = 0; i < g_hand.size(); i++)
	{
		out[i * 2]     = g_hand[i].first;
		out[i * 2 + 1] = g_hand[i].second;
	}
	return (int)g_hand.size();
}

// --- 難易度プロファイルの問い合わせ(UI がセレクトボックスを組み立てるのに使う) ---
EMSCRIPTEN_KEEPALIVE int yon_profile_num(void)     { return PROFILE_NUM; }
EMSCRIPTEN_KEEPALIVE int yon_profile_default(void) { return PROFILE_DEFAULT; }
EMSCRIPTEN_KEEPALIVE int yon_profile_current(void) { return g_profile; }   // -1 = カスタム
EMSCRIPTEN_KEEPALIVE const char* yon_profile_name(int i)
{
	if (i < 0 || i >= PROFILE_NUM) return "";
	return PROFILES[i].name;
}
// bucket: 0 = 序盤 / 1 = 中盤1 / 2 = 中盤2 / 3 = 終盤。戻り値は読み手数 N
EMSCRIPTEN_KEEPALIVE int yon_profile_plies(int i, int bucket)
{
	if (i < 0 || i >= PROFILE_NUM) return 0;
	const DifficultyProfile& p = PROFILES[i];
	switch (bucket)
	{
		case 0: return p.n_open;
		case 1: return p.n_mid1;
		case 2: return p.n_mid2;
		case 3: return p.n_end;
		default: return 0;
	}
}
// bucket の開始手数(UI がプリセットを表へ流し込むのに使う)
EMSCRIPTEN_KEEPALIVE int yon_profile_turn(int bucket)
{
	return (bucket >= 0 && bucket < 4) ? PROFILE_TURNS[bucket] : 0;
}

// --- モデルの問い合わせ ---
EMSCRIPTEN_KEEPALIVE int yon_model_num(void)     { return MODEL_NUM; }
EMSCRIPTEN_KEEPALIVE int yon_model_current(void) { return g_model; }
EMSCRIPTEN_KEEPALIVE const char* yon_model_name(int i)   // 探索エンジン名 "alpha" / "core"
{
	if (i < 0 || i >= MODEL_NUM) return "";
	return ENGINE_NAME[MODELS[i].engine];
}
EMSCRIPTEN_KEEPALIVE const char* yon_model_weights(int i) { return model_weights_name(i); }
EMSCRIPTEN_KEEPALIVE int yon_model_available(int i) { return model_ok(i) ? 1 : 0; }
EMSCRIPTEN_KEEPALIVE int yon_model_default(void) { return MODEL_DEFAULT; }

// --- スケジュールの問い合わせ ---
EMSCRIPTEN_KEEPALIVE int yon_schedule_len(void)      { return g_sched_len; }
EMSCRIPTEN_KEEPALIVE int yon_schedule_turn(int i)    { return (i >= 0 && i < g_sched_len) ? g_sched_turn[i] : 0; }
EMSCRIPTEN_KEEPALIVE int yon_schedule_ply(int i)     { return (i >= 0 && i < g_sched_len) ? g_sched_ply[i]  : 0; }
EMSCRIPTEN_KEEPALIVE int yon_schedule_max_rows(void) { return SCHED_MAX_ROWS; }
EMSCRIPTEN_KEEPALIVE int yon_schedule_max_ply(void)  { return SCHED_MAX_PLY; }
EMSCRIPTEN_KEEPALIVE int yon_schedule_min_ply(void)  { return SCHED_MIN_PLY; }
// 現局面で実際に使われる読み手数 N(UI のヒント表示用)
EMSCRIPTEN_KEEPALIVE int yon_current_ply(void)
{
	yon_init();
	return yon_depth_target(g_board.turn(), 0) + 1;
}

} // extern "C"

// MODULARIZE ビルドではモジュール生成時に一度だけ走る。
// native のテストハーネスから使う場合は -DYON_NO_MAIN で無効化する。
#ifndef YON_NO_MAIN
int main()
{
	yon_init();
	return 0;
}
#endif
