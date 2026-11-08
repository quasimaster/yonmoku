// =============================================================================
//  test_engine_api.cpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  engine_api.cpp を Web にせずネイティブでビルドして確かめるテスト。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
// engine_api.cpp の native 検証ハーネス(Web ビルドには含めない)。
//   g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
//       code/web/engine_api.cpp code/web/test_engine_api.cpp -o build/test_api.exe
//
// 検証内容:
//   1. AI vs AI で 1局完走し、盤面・勝敗・棋譜が矛盾しないこと
//   2. undo が「AI 手 + 人間手」を正しく巻き戻すこと
//   3. 難易度プロファイルが実際に読み手数を変えていること(思考時間・ノード数で確認)
//   4. 評価値が白視点に正規化されていること(先後を入れ替えて符号を確認)

#include <cstdio>
#include <cstdlib>

extern "C" {
	void   yon_init(void);
	void   yon_new_game(int human_is_white, int profile);
	void   yon_set_profile(int profile);
	int    yon_play(int x, int y);
	int    yon_think(void);
	int    yon_analyze(void);
	int    yon_undo(void);
	unsigned long long yon_black(void);
	unsigned long long yon_white(void);
	int    yon_legal_columns(void);
	int    yon_landing_z(int x, int y);
	int    yon_status(void);
	int    yon_turn(void);
	int    yon_move_count(void);
	int    yon_black_to_move(void);
	int    yon_last_score(void);
	int    yon_last_is_mate(void);
	double yon_last_ms(void);
	double yon_last_nodes(void);
	double yon_win_rate_black(void);
	unsigned long long yon_win_line(void);
	int    yon_profile_num(void);
	const char* yon_profile_name(int i);
	int    yon_profile_plies(int i, int bucket);
	int    yon_hand(int* out);
}

static int failures = 0;
static void check(bool ok, const char* msg)
{
	printf("  [%s] %s\n", ok ? "OK" : "NG", msg);
	if (!ok) failures++;
}

static int popcount64(unsigned long long v)
{
	int c = 0; while (v) { v &= v - 1; c++; } return c;
}

int main()
{
	yon_init();

	printf("=== 1. profile table ===\n");
	for (int i = 0; i < yon_profile_num(); i++)
	{
		printf("  profile %d (%s): N = %d / %d / %d / %d\n", i, yon_profile_name(i),
		       yon_profile_plies(i, 0), yon_profile_plies(i, 1),
		       yon_profile_plies(i, 2), yon_profile_plies(i, 3));
	}
	check(yon_profile_plies(3, 0) == 10 && yon_profile_plies(3, 1) == 10 &&
	      yon_profile_plies(3, 2) == 12 && yon_profile_plies(3, 3) == 26,
	      "profile 3 (standard) == current CLI (10/10/12/26)");

	printf("\n=== 2. AI vs AI full game (profile 0, fast) ===\n");
	yon_new_game(1, 0);
	int guard = 0;
	while (yon_status() == 0 && guard++ < 70)
	{
		const int sq = yon_think();
		if (sq < 0) break;
	}
	printf("  moves=%d status=%d (0=cont 1=white 2=black 3=draw)\n", yon_move_count(), yon_status());
	check(yon_status() != 0, "game finished");
	check(yon_move_count() == popcount64(yon_black()) + popcount64(yon_white()),
	      "stone count matches move count");
	check(popcount64(yon_black()) - popcount64(yon_white()) == (yon_move_count() % 2), "white/black balance");
	if (yon_status() == 1 || yon_status() == 2)
		check(popcount64(yon_win_line()) == 4, "win line has exactly 4 cells");
	else
		check(yon_move_count() == 64, "draw means full board");

	printf("\n=== 3. human vs AI + undo (human=white, profile 0) ===\n");
	yon_new_game(1, 0);
	// 人間(白)が先。人間 → AI → 人間 → AI と 4手進める
	check(yon_black_to_move() == 1, "white moves first");
	check(yon_play(0, 0) == 0, "human plays (0,0)");
	check(yon_think() >= 0, "AI replies");
	check(yon_play(1, 1) == 0, "human plays (1,1)");
	check(yon_think() >= 0, "AI replies");
	const int before = yon_move_count();
	check(before == 4, "4 moves played");
	const int after = yon_undo();
	printf("  undo: %d -> %d moves\n", before, after);
	check(after == 2, "undo removed AI move + human move");
	check(yon_black_to_move() == 1, "it is human(white) turn again after undo");
	check(yon_landing_z(1, 1) == 0, "the undone cell (1,1) is empty again");

	printf("\n=== 4. score is normalised to WHITE view ===\n");
	// 同じ手順を「人間=白(AI=黒)」と「人間=黒(AI=白)」で走らせ、
	// AI の評価値が白視点で一貫していることを確認する。
	yon_new_game(1, 2);          // AI = 黒
	yon_play(0, 0);
	yon_think();
	const int score_ai_black = yon_last_score();
	const double wr_black = yon_win_rate_black();
	printf("  AI=black after human(0,0): score_white=%d  white_win_rate=%.1f%%\n", score_ai_black, wr_black);

	yon_new_game(0, 2);          // AI = 白(先手)
	yon_think();
	const int score_ai_white = yon_last_score();
	const double wr_white = yon_win_rate_black();
	printf("  AI=white first move    : score_white=%d  white_win_rate=%.1f%%\n", score_ai_white, wr_white);
	check(score_ai_white > 0, "AI as white evaluates its own position as positive (white view)");
	check(wr_white > 50.0, "white win rate > 50% when white is favoured");
	check(wr_black >= 0.0 && wr_black <= 100.0, "win rate in range");

	printf("\n=== 5. analyze does NOT change the board ===\n");
	yon_new_game(1, 0);
	yon_play(0, 0);
	const int mc = yon_move_count();
	const unsigned long long b0 = yon_black(), w0 = yon_white();
	const int sq = yon_analyze();
	printf("  analyze suggests sq=%d score_white=%d\n", sq, yon_last_score());
	check(sq >= 0, "analyze returned a move");
	check(yon_move_count() == mc, "move count unchanged");
	check(yon_black() == b0 && yon_white() == w0, "board unchanged");

	printf("\n=== 6. difficulty actually changes search effort ===\n");
	double nodes[6];
	for (int p = 0; p < 6; p++)
	{
		yon_new_game(0, p);      // AI = 白、初手を考えさせる
		yon_think();
		nodes[p] = yon_last_nodes();
		printf("  profile %d (%-10s): nodes=%12.0f  %.3f sec\n", p, yon_profile_name(p), nodes[p], yon_last_ms() / 1000.0);
	}
	check(nodes[0] < nodes[3], "profile 0 searches fewer nodes than profile 3");
	check(nodes[3] < nodes[5], "profile 3 searches fewer nodes than profile 5");

	printf("\n=== 7. hand export ===\n");
	yon_new_game(1, 0);
	yon_play(0, 0); yon_think(); yon_play(3, 3);
	int buf[128];
	const int n = yon_hand(buf);
	printf("  hand size=%d : (%d,%d) (%d,%d) (%d,%d)\n", n, buf[0], buf[1], buf[2], buf[3], buf[4], buf[5]);
	check(n == 3, "3 moves exported");
	check(buf[0] == 0 && buf[1] == 0, "first move is (0,0)");
	check(buf[4] == 3 && buf[5] == 3, "third move is (3,3)");

	printf("\n==== %s (%d failures) ====\n", failures == 0 ? "ALL PASS" : "FAILED", failures);
	return failures == 0 ? 0 : 1;
}
