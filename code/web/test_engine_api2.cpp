// engine_api2.cpp の研究モード API の native 検証ハーネス(Web ビルドには含めない)。
//   g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
//       -DUSE_ENDGAME_R2=1 -DUSE_ENDGAME_CUT=1 \
//       code/web/engine_api2.cpp code/web/test_engine_api2.cpp -o build/test_api2.exe
//
// 検証内容(設計書 docs/設計書/Web公開/implementation-plan-research-analysis.md §7.1):
//   1. yon_analyze_ply が着手しない(棋譜・盤面が変わらない)
//   2. N を深めるとノード数が増え、yon_ana_ply が一致する
//   3. 引数チェック(奇数 / 範囲外 / top_k / 終局)
//   4. ★評価関数の先後エントリが「解析局面の手番」に追従する(g_human_is_black に依存しない)
//   5. ★上位 K が厳密(全手フルウィンドウの上位 K と完全一致)
//   6. ★対局経路(yon_analyze = move())の評価値と 1 位の値が一致する
//   7. 同じ条件で 2 回解析すると結果が一致する(再現性)
//   8. deadline_ms が効き、途中結果が返る
//   9. yon_undo_one が 1 手ずつ戻す / yon_undo(2 手戻し)は不変

#include <cstdio>
#include <cstdlib>
#include <cmath>

extern "C" {
	void   yon_init(void);
	void   yon_new_game(int human_is_black, int profile);
	void   yon_set_seed(unsigned int seed);
	int    yon_set_schedule(const int* turns, const int* plies, int len);
	int    yon_set_model(int model);
	int    yon_play(int x, int y);
	int    yon_analyze(void);
	int    yon_undo(void);
	int    yon_undo_one(void);
	int    yon_load(const int* xy, int len);
	unsigned long long yon_black(void);
	unsigned long long yon_white(void);
	int    yon_status(void);
	int    yon_turn(void);
	int    yon_move_count(void);
	int    yon_black_to_move(void);
	int    yon_last_score(void);
	int    yon_last_valid(void);

	int    yon_analyze_ply(int n, int top_k, int fresh_tt, int deadline_ms);
	int    yon_ana_ply(void);
	int    yon_ana_count(void);
	int    yon_ana_sq(int i);
	int    yon_ana_score(int i);
	double yon_ana_winrate(int i);
	int    yon_ana_tied(void);
	int    yon_ana_forced(void);
	int    yon_ana_complete(void);
	double yon_ana_ms(void);
	double yon_ana_nodes(void);
	int    yon_ana_root_moves(void);
	int    yon_ana_max_k(void);
	int    yon_ana_max_ply(void);
	int    yon_ana_full_scores(int n, int* out_sq, int* out_score);
}

static int g_fail = 0;

static void ok(const char* name, bool cond, const char* detail = nullptr)
{
	printf("%s %s", cond ? "[ OK ]" : "[FAIL]", name);
	if (detail) printf("  %s", detail);
	printf("\n");
	if (!cond) g_fail++;
}

// 適当な中盤局面(合法な着手列)。x, y は 0 始まり。
static const int OPENING[] = {
	1,1, 2,2, 1,2, 2,1, 0,0, 3,3, 1,1, 2,2,
	2,1, 1,2, 0,3, 3,0, 1,1, 2,2, 0,0, 3,3,
};
static const int OPENING_N = (int)(sizeof(OPENING) / sizeof(OPENING[0]));

// human_is_black を指定してから OPENING の先頭 moves 手を並べる
static void setup(int human_is_black, int moves)
{
	yon_new_game(human_is_black, -1);
	yon_set_seed(12345);
	const int r = yon_load(OPENING, moves * 2);
	if (r != moves) { printf("  !! yon_load failed: %d\n", r); exit(1); }
}

static const char* sq_str(int sq, char* buf)
{
	if (sq < 0) { snprintf(buf, 24, "(none)"); return buf; }
	snprintf(buf, 24, "(%d,%d,%d)", sq % 4 + 1, (sq / 4) % 4 + 1, sq / 16 + 1);
	return buf;
}

static void dump(const char* tag)
{
	char b[24];
	printf("    %s: N=%2d complete=%d forced=%d roots=%2d tied=%d %.0f ms %.0f nodes\n",
	       tag, yon_ana_ply(), yon_ana_complete(), yon_ana_forced(),
	       yon_ana_root_moves(), yon_ana_tied(), yon_ana_ms(), yon_ana_nodes());
	for (int i = 0; i < yon_ana_count(); i++)
		printf("      %d. %-10s score(black)=%10d  win(black)=%5.1f%%\n",
		       i + 1, sq_str(yon_ana_sq(i), b), yon_ana_score(i), yon_ana_winrate(i));
}

int main()
{
	yon_init();
	printf("=== engine_api2 研究モード 検証 ===\n");
	printf("ANA_MAX_K=%d ANA_MAX_PLY=%d\n\n", yon_ana_max_k(), yon_ana_max_ply());

	// ---- 1. 着手しない ----
	{
		setup(1, 12);
		const int mc = yon_move_count();
		const unsigned long long bb = yon_black(), wb = yon_white();
		const int turn = yon_turn();
		const int r = yon_analyze_ply(8, 3, 1, 0);
		ok("1. yon_analyze_ply が 1 を返す", r == 1);
		ok("1. 手数が変わらない", yon_move_count() == mc);
		ok("1. 盤面が変わらない", yon_black() == bb && yon_white() == wb);
		ok("1. 手番が変わらない", yon_turn() == turn);
		ok("1. 候補手が 3 件", yon_ana_count() == 3);
		dump("N=8");
	}

	// ---- 2. 深めるとノードが増える ----
	{
		setup(1, 12);
		double prev = 0;
		bool mono = true;
		for (int n = 8; n <= 12; n += 2)
		{
			const int r = yon_analyze_ply(n, 3, 0, 0);
			if (r != 1) { mono = false; break; }
			if (yon_ana_ply() != n) { mono = false; break; }
			char t[16]; snprintf(t, sizeof(t), "N=%d", n);
			dump(t);
			if (yon_ana_nodes() <= prev) mono = false;
			prev = yon_ana_nodes();
		}
		ok("2. N=8,10,12 でノード数が単調増加し ana_ply が一致", mono);
	}

	// ---- 3. 引数チェック ----
	{
		setup(1, 12);
		ok("3. 奇数の N を弾く",        yon_analyze_ply(9, 3, 0, 0) == -2);
		ok("3. 小さすぎる N を弾く",    yon_analyze_ply(0, 3, 0, 0) == -2);
		ok("3. 大きすぎる N を弾く",    yon_analyze_ply(66, 3, 0, 0) == -2);
		ok("3. top_k 範囲外を弾く",     yon_analyze_ply(8, 0, 0, 0) == -2 && yon_analyze_ply(8, 6, 0, 0) == -2);
		ok("3. deadline 負値を弾く",    yon_analyze_ply(8, 3, 0, -1) == -2);

		// 終局まで進めて -1 になること
		yon_new_game(1, -1);
		int guard = 0;
		while (yon_status() == 0 && guard++ < 70)
		{
			bool placed = false;
			for (int y = 0; y < 4 && !placed; y++) for (int x = 0; x < 4 && !placed; x++)
				if (yon_play(x, y) != 2) placed = true;
			if (!placed) break;
		}
		ok("3. 終局局面では -1", yon_status() != 0 && yon_analyze_ply(8, 3, 0, 0) == -1);
	}

	// ---- 4. ★先後エントリが手番に追従する ----
	{
		// 12 手進めた局面は turn=13(黒番)。human_is_black を変えても結果は同じはず。
		setup(1, 12);
		const int turn_a = yon_turn();
		yon_analyze_ply(10, 3, 1, 0);
		const int sq_a = yon_ana_sq(0), sc_a = yon_ana_score(0);

		setup(0, 12);
		yon_analyze_ply(10, 3, 1, 0);
		const int sq_b = yon_ana_sq(0), sc_b = yon_ana_score(0);

		char d[96];
		snprintf(d, sizeof(d), "turn=%d  human=黒: %d/%d   human=白: %d/%d", turn_a, sq_a, sc_a, sq_b, sc_b);
		ok("4. g_human_is_black に依存しない(黒番の局面)", sq_a == sq_b && sc_a == sc_b, d);

		// 13 手進めた局面は turn=14(白番)でも同じことを確かめる
		setup(1, 13);
		const int turn_c = yon_turn();
		yon_analyze_ply(10, 3, 1, 0);
		const int sq_c = yon_ana_sq(0), sc_c = yon_ana_score(0);
		setup(0, 13);
		yon_analyze_ply(10, 3, 1, 0);
		const int sq_d = yon_ana_sq(0), sc_d = yon_ana_score(0);
		snprintf(d, sizeof(d), "turn=%d  human=黒: %d/%d   human=白: %d/%d", turn_c, sq_c, sc_c, sq_d, sc_d);
		ok("4. g_human_is_black に依存しない(白番の局面)", sq_c == sq_d && sc_c == sc_d, d);
	}

	// ---- 5. ★上位 K が厳密(全手フルウィンドウと一致)----
	{
		int fsq[16], fsc[16];
		bool all = true;
		char d[128] = "";
		for (int moves = 10; moves <= 14; moves += 2)
		{
			setup(1, moves);
			const int m = yon_ana_full_scores(8, fsq, fsc);
			if (m <= 0) { all = false; break; }

			setup(1, moves);
			if (yon_analyze_ply(8, 3, 1, 0) != 1) { all = false; break; }

			const int k = yon_ana_count() < m ? yon_ana_count() : m;
			for (int i = 0; i < k; i++)
			{
				// 同点があるので「スコアが一致」を必須、マスは同点内で入れ替わりうる
				if (yon_ana_score(i) != fsc[i])
				{
					snprintf(d, sizeof(d), "moves=%d i=%d  multipv=%d  full=%d",
					         moves, i, yon_ana_score(i), fsc[i]);
					all = false;
				}
			}
			if (!all) break;
		}
		ok("5. 上位 3 手のスコアが全手フルウィンドウと完全一致", all, d[0] ? d : nullptr);
	}

	// ---- 6. ★対局経路(move())の評価値と一致 ----
	{
		bool all = true;
		char d[128] = "";
		for (int moves = 10; moves <= 14; moves += 2)
		{
			const int n = 10;
			// yon_analyze は g_human_is_black で sec を決めるので、
			// 解析局面の手番(白番なら sec=true)に合わせて human_is_black を選ぶ。
			// turn = moves + 1。turn が偶数(白番)なら sec=true = human_is_black=1。
			const int turn = moves + 1;
			const int human_is_black = (turn % 2 == 0) ? 1 : 0;

			setup(human_is_black, moves);
			const int turns[1] = { 1 }, plies[1] = { n };
			yon_set_schedule(turns, plies, 1);
			yon_set_seed(12345);
			yon_analyze();
			const int s_think = yon_last_score();

			setup(human_is_black, moves);
			yon_set_schedule(turns, plies, 1);
			yon_analyze_ply(n, 3, 1, 0);
			const int s_ana = yon_ana_score(0);

			// 勝敗を読み切った場合、対局経路は表示用の MATE_SCORE(1e6)、
			// 研究経路は探索が返した INF-turn(≒1e9)になる。表現が違うだけなので符号で照合する。
			const bool solved = (s_think >= 1000000 || s_think <= -1000000)
			                 || (s_ana   >=  100000000 || s_ana <= -100000000);
			const bool agree = solved ? ((s_think > 0) == (s_ana > 0)) : (s_think == s_ana);
			if (!agree)
			{
				snprintf(d, sizeof(d), "moves=%d turn=%d  think=%d  ana=%d", moves, turn, s_think, s_ana);
				all = false;
				break;
			}
		}
		ok("6. 1 位の評価値が yon_analyze(move())と一致", all, d[0] ? d : nullptr);
	}

	// ---- 7. 再現性 ----
	{
		setup(1, 12);
		yon_analyze_ply(10, 3, 1, 0);
		int s1[3], q1[3];
		for (int i = 0; i < 3; i++) { s1[i] = yon_ana_score(i); q1[i] = yon_ana_sq(i); }

		setup(1, 12);
		yon_analyze_ply(10, 3, 1, 0);
		bool same = true;
		for (int i = 0; i < 3; i++) if (s1[i] != yon_ana_score(i) || q1[i] != yon_ana_sq(i)) same = false;
		ok("7. fresh_tt=1 の 2 回実行で結果が一致", same);
	}

	// ---- 8. deadline ----
	{
		setup(1, 8);
		const int r = yon_analyze_ply(16, 3, 1, 1);   // 1 ms = ほぼ確実に途中で切れる
		char d[96];
		snprintf(d, sizeof(d), "ret=%d complete=%d count=%d %.0f ms",
		         r, yon_ana_complete(), yon_ana_count(), yon_ana_ms());
		ok("8. deadline_ms=1 で途中終了し候補手は 1 件以上", r == 0 && yon_ana_complete() == 0 && yon_ana_count() >= 1, d);

		setup(1, 8);
		const int r2 = yon_analyze_ply(8, 3, 1, 600000);   // 10 分なら完走する
		ok("8. deadline が十分なら完走", r2 == 1 && yon_ana_complete() == 1);
	}

	// ---- 9. undo ----
	{
		setup(1, 12);   // human = 黒 → 人間手の index は偶数
		ok("9. undo_one が 1 手ずつ戻す", yon_undo_one() == 11 && yon_undo_one() == 10);
		setup(1, 12);
		ok("9. undo は 2 手戻し(従来どおり)", yon_undo() == 10);
		yon_new_game(1, -1);
		ok("9. 空の盤面で undo_one は 0", yon_undo_one() == 0);
	}

	// ---- 追加: 強制手の検出 ----
	{
		// 同じ列に黒を 3 つ積むと黒は縦のリーチを持つ。黒番なら即勝ち(forced=1)。
		yon_new_game(1, -1);
		yon_play(0, 0); yon_play(3, 3);
		yon_play(0, 0); yon_play(3, 3);
		yon_play(0, 0); yon_play(3, 3);
		// ここで turn=7(黒番)、黒は (0,0) の 4 段目で四目 → 即勝ち
		const int r = yon_analyze_ply(8, 3, 1, 0);
		char d[96];
		snprintf(d, sizeof(d), "ret=%d forced=%d count=%d score=%d",
		         r, yon_ana_forced(), yon_ana_count(), yon_ana_count() ? yon_ana_score(0) : 0);
		ok("A. 即勝ちを forced=1 で返す", r == 1 && yon_ana_forced() == 1 && yon_ana_count() >= 1
		                                  && yon_ana_score(0) > 100000000, d);
		ok("A. 即勝ちでは探索していない(0 ノード)", yon_ana_nodes() == 0);
	}

	// ---- B. 研究 → 対局 で先後エントリが取り残されないこと ----
	{
		// human = 白 → AI は黒(sec = false)。研究で白番の局面(sec = true)を解析してから対局へ戻す。
		const int turns[1] = { 1 }, plies[1] = { 8 };
		setup(0, 13);                       // turn=14 = 白番 → 解析は sec=true
		yon_set_schedule(turns, plies, 1);
		yon_analyze_ply(8, 3, 1, 0);
		yon_analyze();                      // 対局経路。ここで sec=false に戻るはず
		const int mixed = yon_last_score();

		setup(0, 13);                       // 研究を通さない素の値
		yon_set_schedule(turns, plies, 1);
		yon_analyze();
		const int clean = yon_last_score();

		char d[96];
		snprintf(d, sizeof(d), "after research = %d  clean = %d", mixed, clean);
		ok("B. 研究モードを通しても対局経路の評価値が変わらない", mixed == clean, d);
	}

	printf("\n%s (fail = %d)\n", g_fail == 0 ? "ALL PASS" : "FAILED", g_fail);
	return g_fail == 0 ? 0 : 1;
}
