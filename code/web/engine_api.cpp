// ===== 立体四目並べ Web 版 エンジン API =====
// 設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §3
//
// 既存の CLI 実装(main_alpha_pvs_eval_inc_tbl_id.cpp)と同じ探索・評価・盤面・TT を include し、
// 「局面を渡すと着手を返すだけ」の薄い API に作り替えたもの。
//   - 探索本体(evaluate_board)は一切触らない
//   - HumanPlayer / Game::game() のブロッキングループは使わない
//   - OpenMP と教師データ自己対戦ブロックは含めない(Emscripten は OpenMP 非対応)
//   - load_openings() も含めない(人間対局では未使用)
//
// ビルドは web/build.ps1 を参照。

#ifndef USE_ASSERT
#define NDEBUG          // すべての #include より前(assert 無効化)
#endif

#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

// ★ ai_player_pvs_inc_id.hpp の YON_DEPTH_TARGET(turn, level) から呼ばれる。
//    マクロは前処理で展開されるだけなので、テンプレート定義より前に宣言が要る。
inline int yon_depth_target(int turn, int level);

#include "../common.hpp"
#include "../board.hpp"
#include "../player.hpp"
#include "../game.hpp"
#include "../tt.hpp"
#include "../board_inc.hpp"
#include "../ai_player_pvs_inc_id.hpp"
#include "../evaluate_alpha_inc_tbl.hpp"

#include <cmath>

#ifdef __EMSCRIPTEN__
#include <emscripten/emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif

using AI = AIPlayerPVSIncID<int(*)(const BoardInc&, unsigned long long, unsigned long long, unsigned long long)>;

// ===== 難易度プロファイル(設計書 §2.2)=====
// 値は「読み手数 N」。内部の探索深さは d = N - 1。N は必ず偶数(評価関数の偶数手読み前提)。
// ID 3「標準」は現行 CLI と完全同一: 序盤 N=10 / 以降 10 / 12 / 26 → d = 9 / 9 / 11 / 25。
struct DifficultyProfile
{
	const char* name;
	int n_open;    // turn < 21
	int n_mid1;    // 21 <= turn < 29
	int n_mid2;    // 29 <= turn < 37
	int n_end;     // turn >= 37
	int tt_bits;   // 置換表サイズ(モバイル配慮で弱いプロファイルは小さく)
};

static const DifficultyProfile PROFILES[] = {
	{ "\xe5\x85\xa5\xe9\x96\x80",                          4,  4,  6, 10, 20 },  // 入門
	{ "\xe3\x82\x84\xe3\x81\x95\xe3\x81\x97\xe3\x81\x84",  6,  6,  8, 14, 20 },  // やさしい
	{ "\xe3\x81\xb5\xe3\x81\xa4\xe3\x81\x86",              8,  8, 10, 20, 22 },  // ふつう
	{ "\xe6\xa8\x99\xe6\xba\x96",                         10, 10, 12, 26, 22 },  // 標準(既定 = 現行 CLI 相当)
	{ "\xe5\xbc\xb7\xe3\x81\x84",                         12, 12, 14, 26, 22 },  // 強い
	{ "\xe6\x9c\x80\xe5\xbc\xb7",                         12, 14, 16, 26, 22 },  // 最強
};
static const int PROFILE_NUM = (int)(sizeof(PROFILES) / sizeof(PROFILES[0]));
static const int PROFILE_DEFAULT = 3;

// ===== 内部状態(設計書 §3.2)=====
static Board                     g_board;              // 現在局面(Me = 手番側)
static vector<pair<int, int> >   g_hand;               // ★棋譜。唯一の真実の源
static Game*                     g_dummy   = nullptr;  // AI が game->evaluates*_tmp[] を書くために必須
static AI*                       g_ai      = nullptr;
static bool                      g_human_is_black = true;
static int                       g_profile = PROFILE_DEFAULT;
static int                       g_tt_bits = 0;        // 現在の AI が持つ TT のビット数
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

// ===== 読み深さフック(設計書 §2.4)=====
// ai_player_pvs_inc_id.hpp の d_target がこれを呼ぶ。level は AI インスタンスの読み手数だが、
// 中盤以降のバケットはプロファイル表から引くので使わない。
inline int yon_depth_target(int turn, int level)
{
	(void)level;
	const DifficultyProfile& p = PROFILES[g_profile];
	const int n = turn >= 37 ? p.n_end
	            : turn >= 29 ? p.n_mid2
	            : turn >= 21 ? p.n_mid1
	                         : p.n_open;
	return n - 1;   // 総読み手数 N = d + 1
}

// ===== 補助 =====

// 絶対色のビットボード(設計書 §3.4)。Board::print() と同じ変換。
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

// 置換表を空にする(設計書 §2.5)。new_search() の世代更新では不十分。
static inline void clear_tt()
{
	if (!g_ai) return;
	for (TTEntry& e : g_ai->tt.table) e.bound = TT_EMPTY;
	g_ai->tt.generation = 0;
}

// 棋譜 g_hand から盤面を再生する(設計書 §3.5)。undo / 棋譜読込 / 局面ジャンプが共有する。
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

// 指定プロファイルで AI を用意する。tt_bits が変わるときだけ作り直す。
static void ensure_ai(int profile)
{
	if (profile < 0 || profile >= PROFILE_NUM) profile = PROFILE_DEFAULT;
	g_profile = profile;
	const DifficultyProfile& p = PROFILES[profile];

	if (!g_ai || g_tt_bits != p.tt_bits)
	{
		delete g_dummy; g_dummy = nullptr;
		delete g_ai;    g_ai = nullptr;
		g_ai = new AI(p.n_open, evaluate_pointfir_cont_layer_intersection_rit, p.tt_bits);
		g_tt_bits = p.tt_bits;
		g_dummy = new Game(g_ai, g_ai, false, {});   // Game ctor は set_verbose を呼ぶので非 nullptr が必須
		g_ai->set_game(g_dummy);
	}
	else
	{
		clear_tt();
	}
	g_ai->level = p.n_open;                          // 序盤バケットの読み手数(history のスケールにも使われる)
	g_ai->set_random(0);                             // MVP ではランダム手を使わない
	// AI が持つ色に応じた評価関数(先手用 / 後手用)
	g_ai->evaluate_func = g_human_is_black ? evaluate_pointsec_cont_layer_intersection_rit
	                                       : evaluate_pointfir_cont_layer_intersection_rit;
}

// 探索して最善手と評価値を得る。**盤面は変更しない**(設計書 §3.3 の think / analyze 共通部)。
//   out_sq          : 着手マス 0..63
//   out_score_mover : 手番側から見た評価値
//   out_mate        : 即勝ち手を見つけた(探索を経ていないので評価値は無い)
static void search_only(int* out_sq, int* out_score_mover, bool* out_mate)
{
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
	const pair<int, int> xy = g_ai->move(g_board);   // Board は値渡しなので g_board は変わらない
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

// 手番側視点の評価値を黒視点に正規化する(設計書 §4.6.1)。
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

// ===== 公開 API =====
extern "C" {

// --- 状態を変える関数 ---

EMSCRIPTEN_KEEPALIVE void yon_init(void)
{
	if (g_inited) return;
	init_lines();
	init_sq_lines();
	init_cnt_tbl();
	ensure_ai(PROFILE_DEFAULT);
	g_inited = true;
}

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
	ensure_ai(profile);
	clear_tt();                      // プロファイルが同じでも新規対局では必ずクリア
}

EMSCRIPTEN_KEEPALIVE void yon_set_profile(int profile)
{
	yon_init();
	ensure_ai(profile);
	clear_tt();                      // 深い設定の表を浅い設定が再利用しないように(設計書 §2.5)
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

// 現局面を探索するが着手はしない(棋譜解析用。MVP では UI から未使用)
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

// 「直前の AI 手 + 自分の手」を巻き戻す(設計書 §3.5)。戻り値: 巻き戻し後の手数
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

// 勝利した 4 石のビット(設計書 §3.6)。勝敗が付いていなければ 0
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
EMSCRIPTEN_KEEPALIVE int yon_profile_current(void) { return g_profile; }
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
