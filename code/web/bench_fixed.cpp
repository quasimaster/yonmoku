// native / WASM を「同一局面・同一探索」で比較するためのベンチ(Web ビルドには含めない)。
// 同じ手順を yon_load で再現し、yon_analyze で探索させる。
// **ノード数が native と WASM で完全一致すれば、同じ仕事量を測れている**ことの証明になる。
//   g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
//       code/web/engine_api.cpp code/web/bench_fixed.cpp -o build/bench_fixed.exe
// 対応する WASM 側は web/bench_fixed.mjs。

#include <cstdio>
#include <cstring>

extern "C" {
	void   yon_init(void);
	void   yon_new_game(int human_is_black, int profile);
	int    yon_load(const int* xy, int len);
	int    yon_analyze(void);
	double yon_last_ms(void);
	double yon_last_nodes(void);
	int    yon_last_score(void);
	int    yon_turn(void);
}

// bench_endgame_selfplay の game 3 の実戦譜(x, y を 1 文字ずつ並べたもの)
static const char* GAME =
	"000000003322222230033231030320101010031113111131102101210121210113221313113223233333012333323223313130202020121212120202";

// 計測する局面(先頭から何手進めるか)と使用プロファイル
static const int PLIES[]   = { 0, 6, 14, 24, 34, 44 };
static const int PROFILE   = 3;   // 標準(= 現行 CLI 相当)

int main()
{
	yon_init();
	printf("%8s %6s %12s %12s %10s\n", "plies", "turn", "nodes", "ms", "score");
	printf("--------------------------------------------------------\n");

	int xy[128];
	for (int k = 0; k < (int)(sizeof(PLIES) / sizeof(PLIES[0])); k++)
	{
		const int n = PLIES[k];
		for (int i = 0; i < n; i++)
		{
			xy[i * 2]     = GAME[i * 2]     - '0';
			xy[i * 2 + 1] = GAME[i * 2 + 1] - '0';
		}
		yon_new_game(1, PROFILE);
		if (yon_load(xy, n * 2) < 0) { printf("load failed at plies=%d\n", n); continue; }
		yon_analyze();
		printf("%8d %6d %12.0f %12.1f %10d\n", n, yon_turn(), yon_last_nodes(), yon_last_ms(), yon_last_score());
		fflush(stdout);
	}
	return 0;
}
