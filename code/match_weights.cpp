#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif

// 2 つの重みモデルを対戦させ、強さの差を勝率で測るハーネス(マルチスレッド)。
// 設計: docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md §2.6
//
// 探索・評価・盤面・TT は main_alpha_pvs_eval_inc_tbl_id.cpp と完全に同一のものを include する。
// 重みは weights/alpha/(version 1)と weights/core/(version 2。核の項 core 付き、main_core.cpp と同じ評価)の両方を受け付け、
// 混在(alpha 対 core)の対戦もできる。
// 両プレイヤーとも set_random(0)。棋譜のばらつきは「評価値が同点の最善手からの乱択」だけから生じる。
//
// ■ 使い方
//   match_weights <A.txt|builtin> <B.txt|builtin> hirate   <総局数(偶数)>        [並列数=1] [level=10]
//   match_weights <A.txt|builtin> <B.txt|builtin> openings <1スレッドあたり周回数> [並列数=1] [level=10]
//
//   hirate   : 平手。総局数を先後の組(2 局)単位で並列数に割り振り、各スレッドは A 先手 / B 先手を交互に打つ。
//   openings : unique_opening/unique_openings_4.txt の全定跡を、各スレッドが指定周回数ずつ回す。
//              定跡 1 本につき A 先手 / B 先手の 2 局。総局数 = 並列数 × 周回数 × 定跡数 × 2。
//
//   例: match_weights weights/alpha/ver8_2.txt weights/alpha/ver8_2_5.txt hirate 10000 16 8
//       match_weights weights/alpha/ver8_2_5.txt weights/core/ver1_0_core.txt hirate 10000 16 8
//
// ■ 乱数
//   同点手の乱択は AI_RNG(ai_player_pvs_inc_id.hpp)経由で、スレッドごとの生成器 g_match_rng を使う。
//   スレッド t のシードは 5489 + t(5489 は mt19937 の既定シード)。並列数と引数が同じなら結果は再現する。
//
// ■ メモリ
//   AI 1 体あたり TT 64MB。1 スレッドで 2 体 = 128MB、並列数 16 なら約 2GB。
//
// ビルド:
//   g++ -std=c++17 -O2 -DBENCH code/match_weights.cpp -o match_weights

#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

// 探索内の乱数をスレッドローカルな生成器へ差し替える(common.hpp のグローバル rng はスレッド間で共有されてしまうため)
#define AI_RNG g_match_rng

#include "common.hpp"
inline thread_local mt19937 g_match_rng;

#include "board.hpp"
#include "player.hpp"
#include "game.hpp"
#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc_id.hpp"
#include "evaluate_core.hpp"                // evaluate_alpha_inc_tbl_w.hpp(EvalFn) + 核の項(EvalFnCore)
#include <cerrno>
#include <thread>
#include <mutex>
#include <atomic>

// 重みは EvalWeightsCore で持つ(version 1 = weights/alpha/ も version 2 = weights/core/ も読める)。
// core が 1 つでも非 0 のモデルは EvalFnCore、全部 0 のモデル(version 1 / builtin)は従来どおり EvalFn で評価する。
// EvalFnCore は core = 0 でも評価値は EvalFn と同じだが、核の項の計算が葉ごとに入るので、
// core 無しのモデルでは EvalFn を直接呼んで改修前と同じ速度・同じノード数に保つ。
struct EvalFnMatch
{
	const EvalWeightsCore* w;
	bool sec;    // false = 先手用エントリ / true = 後手用エントリ
	bool core;   // w->has_core()

	int operator()(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, unsigned long long hand) const
	{
		if (core) return EvalFnCore{w, sec}(board, rMe, rYou, hand);
		return EvalFn{&w->base, sec}(board, rMe, rYou, hand);
	}
};
using AI = AIPlayerPVSIncID<EvalFnMatch>;

#ifdef _WIN32
// 出力は UTF-8。日本語 Windows のコンソール(cmd / PowerShell)は既定で CP932 として表示するため文字化けする。
// 実行中だけコンソールの出力コードページを UTF-8(65001)にし、終了時(Ctrl+C を含む)に元へ戻す。
// windows.h は SIZE などプロジェクトの識別子と衝突するので、使う API だけ宣言する。
extern "C" __declspec(dllimport) unsigned int __stdcall GetConsoleOutputCP(void);
extern "C" __declspec(dllimport) int __stdcall SetConsoleOutputCP(unsigned int cp);
extern "C" __declspec(dllimport) int __stdcall SetConsoleCtrlHandler(int (__stdcall *handler)(unsigned long), int add);

static unsigned int g_orig_console_cp = 0;   // 0 = コンソールが無い(パイプ・ファイルへの出力)か未変更

static void restore_console_cp()
{
	if(g_orig_console_cp) SetConsoleOutputCP(g_orig_console_cp);
}

static int __stdcall on_console_ctrl(unsigned long)
{
	fflush(stdout);
	restore_console_cp();
	return 0;   // 既定の処理(プロセス終了)へ回す
}

static void use_utf8_console()
{
	const unsigned int cp = GetConsoleOutputCP();   // コンソールが無ければ 0
	if(cp == 0 || cp == 65001u) return;
	if(!SetConsoleOutputCP(65001u)) return;
	g_orig_console_cp = cp;
	atexit(restore_console_cp);
	SetConsoleCtrlHandler(on_console_ctrl, 1);
}
#else
static void use_utf8_console() {}
#endif

static const char* const OPENINGS_PATH = "unique_opening/unique_openings_4.txt";
static const unsigned SEED_BASE = 5489u;

// 定跡(重複なし初手列)。bench_endgame_selfplay.cpp の load_openings と同一。
static vector<vector<pair<int, int> > > load_openings(const string& rel_path)
{
	static const char* prefix[] = {"", "../", "../../"};
	ifstream ifs;
	string used;
	for(const char* p : prefix)
	{
		used = string(p) + rel_path;
		ifs.open(used);
		if(ifs) break;
		ifs.clear();
	}
	if(!ifs) { cerr << "openings file not found: " << rel_path << endl; return {}; }

	vector<vector<pair<int, int> > > openings;
	string line;
	while(getline(ifs, line))
	{
		size_t head = line.find_first_not_of(" \t");
		if(head == string::npos || line.compare(head, 2, "{{") != 0) continue;
		vector<int> nums;
		for(size_t i = head; i < line.size(); )
		{
			if(isdigit((unsigned char)line[i]))
			{
				int v = 0;
				while(i < line.size() && isdigit((unsigned char)line[i])) v = v * 10 + (line[i++] - '0');
				nums.push_back(v);
			}
			else i++;
		}
		if(nums.empty() || nums.size() % 2 != 0) continue;
		vector<pair<int, int> > op;
		bool ok = true;
		for(size_t i = 0; i < nums.size(); i += 2)
		{
			if(nums[i] < 0 || nums[i] >= SIZE || nums[i + 1] < 0 || nums[i + 1] >= SIZE) { ok = false; break; }
			op.emplace_back(nums[i], nums[i + 1]);
		}
		if(!ok) continue;
		openings.push_back(move(op));
	}
	cerr << "openings loaded: " << openings.size() << " from " << used << endl;
	return openings;
}

// 重みを用意する。"builtin" なら組み込み既定値、それ以外はファイルから読む。
// 読めなければ組み込み既定値へ戻さずに終了する(設計書 §2.4)。
static const EvalWeightsCore* prepare(const char* spec, EvalWeightsCore& slot)
{
	if(string(spec) == "builtin") return &EvalWeightsCore::builtin();
	string err;
	if(!slot.load(spec, &err)) { cerr << "weights error: " << err << endl; exit(1); }
	return &slot;
}

// 正の整数として読む。数値でない・0 以下・範囲外なら -1
static long long parse_positive(const char* s)
{
	char* end = nullptr;
	errno = 0;
	const long long v = strtoll(s, &end, 10);
	if(errno != 0 || end == s || *end != '\0' || v <= 0) return -1;
	return v;
}

// 1 スレッド分の集計。[0] A が先手 / [1] B が先手。各要素は A から見た 勝 / 敗 / 分
struct Tally
{
	long long win[2] = {}, lose[2] = {}, draw[2] = {};
	double sec = 0;
	long long nodes = 0;
};

// スレッド間で共有する(A / B / level は読み取り専用。出力は mutex、進捗は atomic)
struct Shared
{
	const EvalWeightsCore* A = nullptr;
	const EvalWeightsCore* B = nullptr;
	int level = 0;
	long long total_games = 0;
	mutex out_mtx;
	atomic<long long> done{0};
};

// 1 局打って t に加算し、1 行出力する。side 0: A 先手 / side 1: B 先手
static void play_one(Shared& sh, Tally& t, int tid, const char* label, const vector<pair<int, int> >& book, int side)
{
	const EvalWeightsCore* black = (side == 0) ? sh.A : sh.B;
	const EvalWeightsCore* white = (side == 0) ? sh.B : sh.A;

	// 先手番は先手用エントリ(fir)、後手番は後手用エントリ(sec)を使う。
	// これは既存の main / bench と同じ割り当てで、色に対応するものであってモデルの識別ではない。
	AI p1(sh.level, EvalFnMatch{black, false, black->has_core()});
	AI p2(sh.level, EvalFnMatch{white, true , white->has_core()});
	p1.set_random(0);
	p2.set_random(0);
	Game game(&p1, &p2, false, book);
	p1.set_game(&game);
	p2.set_game(&game);

#ifdef BENCH
	const long long n0 = g_node_count;   // thread_local
#endif
	const auto st = chrono::steady_clock::now();

	enum State ret = State::Continue;
	int turn = 0;
	while(turn < BOARD_SIZE)
	{
		ret = game.move(turn);
		if(ret == State::End) break;
		turn++;
	}

	const double sec = chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - st).count() / 1e3;
#ifdef BENCH
	const long long nodes = g_node_count - n0;
#else
	const long long nodes = 0;
#endif
	t.sec += sec;
	t.nodes += nodes;

	// 勝者(黒 / 白 / 引分)を A から見た結果へ読み替える
	enum Color result;
	if(ret == State::End) result = (game.board.validate() == Color::White) ? Color::Black : Color::White;
	else result = Color::Draw;

	const char* a_res;
	if(result == Color::Draw)                                  { t.draw[side]++; a_res = "draw"; }
	else if((result == Color::Black) == (side == 0))            { t.win[side]++;  a_res = "A win"; }
	else                                                        { t.lose[side]++; a_res = "B win"; }

	const long long d = ++sh.done;
	char buf[256];
	snprintf(buf, sizeof(buf), "[t%02d] %s %s: moves=%2d %-6s %8.3f sec  nodes=%12lld  (%lld/%lld)\n",
	         tid, label, side == 0 ? "A-black" : "B-black",
	         (int)game.hand.size(), a_res, sec, nodes, d, sh.total_games);
	lock_guard<mutex> lk(sh.out_mtx);
	fputs(buf, stdout);
	fflush(stdout);
}

int main(int argc, char** argv)
{
	use_utf8_console();

	const char* usage =
		"usage:\n"
		"  match_weights <A.txt|builtin> <B.txt|builtin> hirate   <総局数(偶数)>        [並列数=1] [level=10]\n"
		"  match_weights <A.txt|builtin> <B.txt|builtin> openings <1スレッドあたり周回数> [並列数=1] [level=10]\n";
	if(argc < 5 || argc > 7) { cerr << usage; return 2; }

	const string mode = argv[3];
	if(mode != "hirate" && mode != "openings") { cerr << "mode は hirate / openings のどちらか: " << mode << "\n" << usage; return 2; }
	const bool hirate = (mode == "hirate");

	const long long count = parse_positive(argv[4]);
	long long threads     = argc > 5 ? parse_positive(argv[5]) : 1;
	const long long level = argc > 6 ? parse_positive(argv[6]) : 10;
	if(count < 0)   { cerr << (hirate ? "総局数" : "周回数") << "は正の整数: " << argv[4] << endl; return 2; }
	if(threads < 0) { cerr << "並列数は正の整数: " << argv[5] << endl; return 2; }
	if(level < 0 || level > BOARD_SIZE) { cerr << "level は 1〜" << BOARD_SIZE << ": " << argv[6] << endl; return 2; }
	if(hirate && count % 2 != 0) { cerr << "総局数は偶数にしてください(A 先手 / B 先手を同数にするため): " << count << endl; return 2; }

	init_lines();
	init_sq_lines();
	init_eval_tbl();

	static EvalWeightsCore slotA, slotB;
	Shared sh;
	sh.A = prepare(argv[1], slotA);
	sh.B = prepare(argv[2], slotB);
	sh.level = (int)level;

	vector<vector<pair<int, int> > > openings;
	vector<long long> games_of;   // hirate: スレッドごとの局数
	if(hirate)
	{
		// 先後の組(2 局)単位で配り、各スレッドの A 先手 / B 先手を同数に保つ
		const long long pairs = count / 2;
		if(threads > pairs)
		{
			cerr << "並列数 " << threads << " が組数 " << pairs << " を超えるため " << pairs << " に減らします" << endl;
			threads = pairs;
		}
		games_of.assign(threads, 0);
		for(long long t = 0; t < threads; t++) games_of[t] = 2 * (pairs / threads + (t < pairs % threads ? 1 : 0));
		sh.total_games = count;
	}
	else
	{
		openings = load_openings(OPENINGS_PATH);
		if(openings.empty()) { cerr << "no openings; abort" << endl; return 1; }
		sh.total_games = threads * count * (long long)openings.size() * 2;
	}

	// モデルの表示(開始時と集計の先頭の 2 か所で使う)
	const auto print_models = [&]()
	{
		printf("A = %s (%s) core: %s\n", sh.A->base.name.c_str(), argv[1], sh.A->has_core() ? "on" : "off");
		printf("B = %s (%s) core: %s\n", sh.B->base.name.c_str(), argv[2], sh.B->has_core() ? "on" : "off");
	};
	print_models();
	if(hirate)
		printf("config: mode=hirate total_games=%lld threads=%lld (per thread %lld..%lld) level=%lld\n",
		       count, threads, games_of.back(), games_of.front(), level);
	else
		printf("config: mode=openings openings=%d laps_per_thread=%lld threads=%lld total_games=%lld level=%lld\n",
		       (int)openings.size(), count, threads, sh.total_games, level);
	printf("        USE_ENDGAME_R2=%d USE_ENDGAME_CUT=%d seed=%u+thread\n", USE_ENDGAME_R2, USE_ENDGAME_CUT, SEED_BASE);
	fflush(stdout);

	vector<Tally> tally(threads);
	const auto wall_st = chrono::steady_clock::now();
	{
		vector<thread> pool;
		for(int tid = 0; tid < (int)threads; tid++)
		{
			pool.emplace_back([&, tid]()
			{
				g_match_rng.seed(SEED_BASE + (unsigned)tid);
				Tally& t = tally[tid];
				char label[64];
				if(hirate)
				{
					const vector<pair<int, int> > empty_book;
					for(long long i = 0; i < games_of[tid]; i++)
					{
						snprintf(label, sizeof(label), "hirate #%6lld", i);
						play_one(sh, t, tid, label, empty_book, (int)(i % 2));
					}
				}
				else
				{
					for(long long lap = 0; lap < count; lap++)
						for(int g = 0; g < (int)openings.size(); g++)
							for(int side = 0; side < 2; side++)
							{
								snprintf(label, sizeof(label), "lap %lld book %4d", lap, g);
								play_one(sh, t, tid, label, openings[g], side);
							}
				}
			});
		}
		for(thread& th : pool) th.join();
	}
	const double wall = chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now() - wall_st).count() / 1e3;

	Tally sum;
	for(const Tally& t : tally)
	{
		for(int s = 0; s < 2; s++) { sum.win[s] += t.win[s]; sum.lose[s] += t.lose[s]; sum.draw[s] += t.draw[s]; }
		sum.sec += t.sec;
		sum.nodes += t.nodes;
	}

	const long long W = sum.win[0] + sum.win[1], L = sum.lose[0] + sum.lose[1], D = sum.draw[0] + sum.draw[1];
	const long long N = W + L + D;
	printf("--------\n");
	print_models();
	for(int tid = 0; tid < (int)threads; tid++)
	{
		const Tally& t = tally[tid];
		printf("[t%02d] A勝 %lld / B勝 %lld / 分 %lld\n", tid, t.win[0] + t.win[1], t.lose[0] + t.lose[1], t.draw[0] + t.draw[1]);
	}
	printf("A 先手: A勝 %lld / B勝 %lld / 分 %lld\n", sum.win[0], sum.lose[0], sum.draw[0]);
	printf("B 先手: A勝 %lld / B勝 %lld / 分 %lld\n", sum.win[1], sum.lose[1], sum.draw[1]);
	printf("合計  : A勝 %lld / B勝 %lld / 分 %lld  (%lld 局)\n", W, L, D, N);
	if(N) printf("A (%s) の勝率(引分 0.5): %.2f %%\n", sh.A->base.name.c_str(), 100.0 * (W + 0.5 * D) / N);
	printf("wall : %.3f sec\n", wall);
	printf("total: %.3f sec (全局の対局時間の和)\n", sum.sec);
	printf("nodes: %lld\n", sum.nodes);
	return 0;
}
