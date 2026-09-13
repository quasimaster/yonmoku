// 難易度プロファイルごとの実測ハーネス(Web ビルドには含めない)。
// 1 手あたりの最大 / 平均思考時間を測り、ブラウザで実用になる読み手数を決めるために使う。
//   g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
//       code/web/engine_api.cpp code/web/bench_profiles.cpp -o build/bench_profiles.exe
//   引数: [計測するプロファイル番号...]  省略時は全プロファイル

#include <cstdio>
#include <cstdlib>

extern "C" {
	void   yon_init(void);
	void   yon_new_game(int human_is_black, int profile);
	int    yon_think(void);
	int    yon_status(void);
	int    yon_move_count(void);
	int    yon_turn(void);
	double yon_last_ms(void);
	double yon_last_nodes(void);
	int    yon_profile_num(void);
	const char* yon_profile_name(int i);
	int    yon_profile_plies(int i, int bucket);
}

int main(int argc, char** argv)
{
	yon_init();
	printf("%-3s %-10s %-16s %8s %10s %10s %10s %14s\n",
	       "id", "name", "plies(N)", "moves", "total_s", "max_ms", "avg_ms", "nodes");
	printf("---------------------------------------------------------------------------------------------\n");

	for (int i = 0; i < yon_profile_num(); i++)
	{
		if (argc > 1)
		{
			bool wanted = false;
			for (int a = 1; a < argc; a++) if (atoi(argv[a]) == i) wanted = true;
			if (!wanted) continue;
		}

		yon_new_game(0, i);          // AI = 黒。AI vs AI で 1 局完走させる
		double total = 0.0, mx = 0.0, nodes = 0.0;
		int mx_turn = 0, moves = 0;
		int guard = 0;
		while (yon_status() == 0 && guard++ < 70)
		{
			const int t = yon_turn();
			if (yon_think() < 0) break;
			const double ms = yon_last_ms();
			total += ms;
			nodes += yon_last_nodes();
			if (ms > mx) { mx = ms; mx_turn = t; }
			moves++;
		}
		char plies[32];
		snprintf(plies, sizeof(plies), "%d/%d/%d/%d",
		         yon_profile_plies(i, 0), yon_profile_plies(i, 1),
		         yon_profile_plies(i, 2), yon_profile_plies(i, 3));
		printf("%-3d %-10s %-16s %8d %10.2f %10.0f %10.1f %14.0f   (max at turn %d)\n",
		       i, yon_profile_name(i), plies, moves, total / 1000.0, mx, total / (moves ? moves : 1), nodes, mx_turn);
		fflush(stdout);
	}
	return 0;
}
