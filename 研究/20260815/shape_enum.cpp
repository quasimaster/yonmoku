// G_A2 ∧ G_3 ∧ G_T を満たす「柱の高さベクトル」(= 形状)の完全列挙。
//
// 主張(本研究で新たに得た補題):
//   G_A2 ⟹ どのラインも空きマスがちょうど 3 個ではない
//        ⟹ 垂直線(= 柱)の空き数 h も 3 ではない、すなわち h ∈ {0,1,2,4}
//   さらに G_3 ⟹ 段3 の全空き水平線が無い ⟹ T = {h>=2} は各水平/対角ラインと高々 2 点で交わる
//   G_T   ⟹ h>=3 の柱は高々 1 本(= h=4 の柱が高々 1 本)
//
// これらから E = Σh に上限が付くはずである。本プログラムはその上限と形状数を厳密に確定する。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o shape_enum.exe shape_enum.cpp
#include "../../code/common.hpp"
#include "../../code/board.hpp"

static int g_colmask[LINES_NUM];      // ライン i が使う柱の集合
static int g_maxcol[LINES_NUM];       // ライン i が使う柱の最大番号
static int g_need[LINES_NUM][16];     // ライン i が柱 c で使う「空きに必要な最小 h」(0 = 使わない)
static bool g_isH3[LINES_NUM];        // 段3 の水平線か

static int h[16];
static long long g_count = 0;
static long long g_byE[80] = {0};
static int g_bestE = -1;
static int g_bestH[16];
static long long g_nBest = 0;
static bool g_useT = true;            // G_T を課すか
static bool g_use3 = true;            // G_3 を課すか

static bool check_lines(int depth)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		if (g_maxcol[i] != depth) continue;
		int e = 0;
		for (int c = 0; c < 16; c++)
			if (g_need[i][c] && h[c] >= g_need[i][c]) e++;
		if (e == 3) return false;                       // G_A2: 1 石 + 空き 3 のラインは禁止
		if (g_use3 && g_isH3[i] && e == 4) return false; // G_3
	}
	return true;
}

static void dfs(int c, int used4)
{
	if (c == 16)
	{
		int E = 0;
		for (int i = 0; i < 16; i++) E += h[i];
		g_count++;
		g_byE[E]++;
		if (E > g_bestE) { g_bestE = E; g_nBest = 0; for (int i = 0; i < 16; i++) g_bestH[i] = h[i]; }
		if (E == g_bestE) g_nBest++;
		return;
	}
	static const int CAND[4] = {0, 1, 2, 4};
	for (int k = 0; k < 4; k++)
	{
		const int v = CAND[k];
		if (v == 4 && g_useT && used4) continue;
		h[c] = v;
		if (check_lines(c)) dfs(c + 1, used4 + (v == 4));
	}
	h[c] = 0;
}

int main(int argc, char **argv)
{
	init_lines();
	if (argc > 1) g_useT = atoi(argv[1]);
	if (argc > 2) g_use3 = atoi(argv[2]);

	for (int i = 0; i < LINES_NUM; i++)
	{
		g_colmask[i] = 0; g_maxcol[i] = 0;
		for (int c = 0; c < 16; c++) g_need[i][c] = 0;
		int zs[4], n = 0;
		for (int b = 0; b < 64; b++) if (LINES[i] >> b & 1)
		{
			const int c = b & 15, z = b >> 4;
			g_colmask[i] |= 1 << c;
			if (c > g_maxcol[i]) g_maxcol[i] = c;
			g_need[i][c] = 4 - z;                       // 段 z+1 が空 ⟺ h >= 4-z
			zs[n++] = z;
		}
		g_isH3[i] = (zs[0] == 2 && zs[1] == 2 && zs[2] == 2 && zs[3] == 2);
	}

	dfs(0, 0);

	printf("G_T=%d G_3=%d  (h ∈ {0,1,2,4}、全ラインの空き数 != 3)\n", (int)g_useT, (int)g_use3);
	printf("形状数 = %lld,  最大 E = %d (turn = %d),  最大 E の形状数 = %lld\n",
	       g_count, g_bestE, 65 - g_bestE, g_nBest);
	printf("E の分布:\n");
	for (int e = 0; e <= 64; e++) if (g_byE[e])
		printf("   E=%2d (turn=%2d) : %10lld\n", e, 65 - e, g_byE[e]);
	printf("最大 E の形状例 (h[y][x]):\n");
	for (int y = 3; y >= 0; y--)
	{
		printf("   ");
		for (int x = 0; x < 4; x++) printf("%d ", g_bestH[x + 4 * y]);
		printf("\n");
	}
	return 0;
}
