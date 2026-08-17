// 論文 §11.1「推測 1」/ §11.2「推測 2」を、論文が検証していない低 turn 域(大きな E)で叩く。
//
// 論文の補題 21 は「交差する 2 本の全空き H4 ラインがあるとき 7 <= E <= 10」と述べ、
// その根拠で検証を turn 57 / 55 / 53(E = 8 / 10 / 12)に限定している。
// しかし E <= 10 の側は「非満杯な柱がその 7 本しか無い」と暗に仮定しており、成り立たない。
// 本研究の補題 N1(G_A2 ⟹ 全ラインの空き数 != 3 ⟹ 柱の高さ h ∈ {0,1,2,4})と
// 補題 N2(G_3 ⟹ T = {h>=2} は各水平/対角ラインと高々 2 点で交わる ⟹ |T| <= 8)より
// ゲート G_A2 ∧ G_T ∧ G_3 を満たす局面の空きマス数は E <= 26(turn >= 39)であり、
// 交差ケースは E = 26 まで起こりうる。本プログラムはその未検証域を直接構成で探索する。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o deep_search.exe deep_search.cpp
// 実行:   ./deep_search.exe <turn> <試行回数> [seed] [dump件数]
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;
static const ull M1 = 0x000000000000ffffuLL, M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL, M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

static ull rs = 88172645463325252uLL;
static inline ull rnd() { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (unsigned)n); }

// ------------------------------------------------------------------ 厳密解
struct TTE { ull me, you; int val; };
static const int TTBITS = 25;
static vector<TTE> g_tt(1u << TTBITS);
static inline ull mix(ull x)
{ x ^= x >> 33; x *= 0xff51afd7ed558ccduLL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53uLL; return x ^ (x >> 33); }
static long long g_nodes = 0;

static int solve(const Board &b)
{
	g_nodes++;
	ull hand = b.valid_move();
	if (!hand) return 0;
	const ull rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou) { if (__builtin_popcountll(hand & rYou) > 1) return -1; hand &= rYou; }
	const ull key = mix(b.Me * 0x9e3779b97f4a7c15uLL ^ mix(b.You));
	TTE &e = g_tt[key & ((1u << TTBITS) - 1)];
	if (e.me == b.Me && e.you == b.You) return e.val;
	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand; hand ^= bit;
		const int v = -solve(b.place_fast_clone(bit));
		if (v > best) best = v;
		if (best == 1) break;
	}
	e.me = b.Me; e.you = b.You; e.val = best;
	return best;
}

static int ruleR2(int turn, ull rMe, ull rYou)
{
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rB = (now == Color::Black) ? rMe : rYou, rW = (now == Color::Black) ? rYou : rMe;
	for (int m = 1; m <= 4; m++)
	{
		if ((m & 1) && (rB & MASK[m])) return now == Color::Black ? +1 : -1;
		if (!(m & 1) && (rW & MASK[m])) return now == Color::White ? +1 : -1;
	}
	return 0;
}

// ------------------------------------------------------------------ 形状の完全列挙
// h ∈ {0,1,2,4}(補題 N1)、h=4 は高々 1 本(G_T)、全ラインの空き数 != 3(G_A2)、
// 段3 の全空き水平線が無い(G_3)。
static int g_need[LINES_NUM][16], g_maxcol[LINES_NUM];
static bool g_isH3[LINES_NUM];
static int h[16];
static vector<array<unsigned char, 16>> g_shapes;
static int g_targetE;
static int g_onlyinf = 0, g_needCross = 0;

static const int COLSET0[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},
	{0,5,10,15}, {3,6,9,12},
};

// 形状だけで決まる量: 「全空き H4 ライン(4 柱とも非満杯)で、埋没しうる柱(h>=2)を含むもの」
// = 攻撃側が埋没した段4 リーチを作りうるライン。2 本が柱を共有すれば「交差ケース」。
static int danger_lines(const int hh[16], bool &cross)
{
	int list[10], n = 0;
	for (int k = 0; k < 10; k++)
	{
		bool live = true; int t = 0;
		for (int j = 0; j < 4; j++)
		{
			const int c = COLSET0[k][j];
			if (hh[c] == 0) { live = false; break; }
			if (hh[c] >= 2) t++;
		}
		if (live && t >= 1) list[n++] = k;
	}
	cross = false;
	for (int i = 0; i < n && !cross; i++)
		for (int j = i + 1; j < n && !cross; j++)
			for (int u = 0; u < 4; u++)
				for (int v = 0; v < 4; v++)
					if (COLSET0[list[i]][u] == COLSET0[list[j]][v]) cross = true;
	return n;
}

static bool check_lines(int depth)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		if (g_maxcol[i] != depth) continue;
		int e = 0;
		for (int c = 0; c < 16; c++) if (g_need[i][c] && h[c] >= g_need[i][c]) e++;
		if (e == 3) return false;
		if (g_isH3[i] && e == 4) return false;
	}
	return true;
}

static void dfs(int c, int used4, int sum)
{
	if (sum > g_targetE) return;
	if (c == 16)
	{
		if (sum != g_targetE) return;
		bool cross = false;
		const int nd = danger_lines(h, cross);
		if (g_needCross == 1 && !cross) return;              // 交差ケースだけ
		if (g_needCross == 2 && nd == 0) return;             // 危険ラインが 1 本以上
		array<unsigned char, 16> a;
		for (int i = 0; i < 16; i++) a[i] = (unsigned char)h[i];
		g_shapes.push_back(a);
		return;
	}
	static const int CAND[4] = {0, 1, 2, 4};
	for (int k = 0; k < 4; k++)
	{
		const int v = CAND[k];
		if (v == 4 && used4) continue;
		h[c] = v;
		if (check_lines(c)) dfs(c + 1, used4 + (v == 4), sum + v);
	}
	h[c] = 0;
}

// ------------------------------------------------------------------ 着色
static ull g_empty, g_hand;
static int g_ecount[LINES_NUM];
static int g_cells[64], g_ncell;

static void setup_shape(const array<unsigned char, 16> &a)
{
	for (int c = 0; c < 16; c++) h[c] = a[c];
	g_empty = 0;
	for (int c = 0; c < 16; c++)
		for (int k = 0; k < h[c]; k++) g_empty |= 1uLL << (c + 16 * (3 - k));
	const ull occ = ~g_empty;
	g_hand = (occ << 16 | M1) & ~occ;
	g_ncell = 0;
	for (int i = 0; i < 64; i++) if (!(g_empty >> i & 1)) g_cells[g_ncell++] = i;
	for (int i = 0; i < LINES_NUM; i++) g_ecount[i] = __builtin_popcountll(LINES[i] & g_empty);
}

// G_A2 + 制約(C) + 決着済でない、の違反数
static int energy(ull B, ull W)
{
	int e = 0;
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int ec = g_ecount[i];
		if (ec >= 3) continue;                       // 形状より ec==4 のみ。全空きラインは常に合法
		const int cb = __builtin_popcountll(B & LINES[i]), cw = __builtin_popcountll(W & LINES[i]);
		if (ec == 0) { if (cb == 4 || cw == 4) e++; }                 // 決着済
		else if (ec == 1)
		{
			if (cb == 3 || cw == 3) { if (LINES[i] & g_empty & g_hand) e++; }   // 制約(C) 違反
		}
		else { if (cb == 2 || cw == 2) e++; }        // G_A2 違反(ec==2 の単色)
	}
	return e;
}

static bool color_it(int turn, ull &B, ull &W)
{
	const int stones = turn - 1, nb = (stones + 1) / 2;
	if (g_ncell != stones) return false;
	int idx[64];
	for (int i = 0; i < g_ncell; i++) idx[i] = i;
	for (int i = g_ncell - 1; i > 0; i--) { const int j = rndi(i + 1); const int t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
	B = W = 0;
	for (int i = 0; i < g_ncell; i++) (i < nb ? B : W) |= 1uLL << g_cells[idx[i]];
	int cur = energy(B, W);
	for (int step = 0; step < 40000 && cur > 0; step++)
	{
		ull bb = B, ww = W;
		int pb = rndi(nb), pw = rndi(g_ncell - nb);
		while (pb--) bb &= bb - 1;
		while (pw--) ww &= ww - 1;
		const ull p = bb & -bb, q = ww & -ww;
		const ull B2 = (B ^ p) | q, W2 = (W ^ q) | p;
		const int e2 = energy(B2, W2);
		if (e2 <= cur) { B = B2; W = W2; cur = e2; }
	}
	return cur == 0;
}

static bool reachable(ull B, ull W)
{
	const int stones = __builtin_popcountll(B | W);
	for (int trial = 0; trial < 20000; trial++)
	{
		int fill[16] = {0}; bool ok = true;
		for (int k = 0; k < stones; k++)
		{
			const bool wantBlack = ((k & 1) == 0);
			int cand[16], nc = 0;
			for (int c = 0; c < 16; c++)
			{
				if (fill[c] >= 4 - h[c]) continue;
				const int i = c + 16 * fill[c];
				if (((B >> i & 1) != 0) == wantBlack) cand[nc++] = c;
			}
			if (!nc) { ok = false; break; }
			fill[cand[rndi(nc)]]++;
		}
		if (ok) return true;
	}
	return false;
}

// ------------------------------------------------------------------ ゲート確認(独立に再計算)
static bool gate_A2(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]), cy = __builtin_popcountll(b.You & LINES[i]);
		if (cy == 0 && (cm == 1 || cm == 2)) return false;
		if (cm == 0 && (cy == 1 || cy == 2)) return false;
	}
	return true;
}
static const int COLSET[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},
	{0,5,10,15}, {3,6,9,12},
};
static bool gate_3(const Board &b)
{
	const ull occ = b.Me | b.You;
	for (int k = 0; k < 10; k++)
	{
		bool all = true;
		for (int j = 0; j < 4; j++) if (occ >> (COLSET[k][j] + 32) & 1) { all = false; break; }
		if (all) return false;
	}
	return true;
}
static bool gate_T(const Board &b) { return __builtin_popcountll(~(b.Me | b.You) & M2) <= 1; }

static void dump(const Board &b, ull B, ull W)
{
	const int turn = b.turn();
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const ull rB = (now == Color::Black) ? rMe : rYou, rW = (now == Color::Black) ? rYou : rMe;
	const ull occ = b.Me | b.You, hand = b.valid_move();
	printf("  turn=%d(手番=%s) 厳密解=%+d R2=%+d | G_A2=%d G_T=%d G_3=%d | 到達可能=%s\n",
	       turn, now == Color::Black ? "黒" : "白", solve(b), ruleR2(turn, rMe, rYou),
	       gate_A2(b), gate_T(b), gate_3(b), reachable(B, W) ? "YES" : "不明");
	b.print();
	printf("  柱の高さ:");
	for (int c = 0; c < 16; c++) if (h[c]) printf(" (x%d,y%d)=%d", (c & 3) + 1, (c >> 2) + 1, h[c]);
	printf("\n  リーチ:");
	for (int i = 0; i < 64; i++)
	{
		if (occ >> i & 1) continue;
		if (!((rB | rW) >> i & 1)) continue;
		printf("  (x%d,y%d,段%d)%s%s%s", X(i) + 1, Y(i) + 1, Z(i) + 1,
		       (rB >> i & 1) ? "[黒]" : "", (rW >> i & 1) ? "[白]" : "", (hand >> i & 1) ? "[即置可]" : "[埋没]");
	}
	printf("\n  最善手順:");
	Board cur = b;
	for (int ply = 0; ply < 40; ply++)
	{
		ull hh = cur.valid_move();
		if (!hh) { printf("  →引き分け"); break; }
		const char *who = ((cur.turn() - 1) & 1) ? "白" : "黒";
		const ull rM = Board::reach(cur.Me) & ~cur.You;
		if (hh & rM) { const int i = __builtin_ctzll(hh & rM); printf("  %s(x%d,y%d,段%d)*勝ち", who, X(i)+1, Y(i)+1, Z(i)+1); break; }
		const ull rY = Board::reach(cur.You) & ~cur.Me;
		if (hh & rY) hh &= rY;
		int best = -2; ull bb = 0;
		for (ull x = hh; x; x &= x - 1) { const ull bit = x & -x; const int v = -solve(cur.place_fast_clone(bit)); if (v > best) { best = v; bb = bit; } }
		const int i = __builtin_ctzll(bb);
		printf("  %s(x%d,y%d,段%d)", who, X(i)+1, Y(i)+1, Z(i)+1);
		cur = cur.place_fast_clone(bb);
	}
	printf("\n");
	fflush(stdout);
}

int main(int argc, char **argv)
{
	init_lines();
	const int turn = argc > 1 ? atoi(argv[1]) : 50;
	const long long trials = argc > 2 ? atoll(argv[2]) : 20000;
	if (argc > 3) rs = (ull)atoll(argv[3]) * 0x9e3779b97f4a7c15uLL + 12345;
	const int maxdump = argc > 4 ? atoi(argv[4]) : 3;
	if (argc > 5) g_onlyinf = atoi(argv[5]);
	if (argc > 6) g_needCross = atoi(argv[6]);
	const int E = 65 - turn;

	for (int i = 0; i < LINES_NUM; i++)
	{
		g_maxcol[i] = 0;
		for (int c = 0; c < 16; c++) g_need[i][c] = 0;
		int zs[4], n = 0;
		for (int b = 0; b < 64; b++) if (LINES[i] >> b & 1)
		{
			const int c = b & 15, z = b >> 4;
			if (c > g_maxcol[i]) g_maxcol[i] = c;
			g_need[i][c] = 4 - z;
			zs[n++] = z;
		}
		g_isH3[i] = (zs[0] == 2 && zs[1] == 2 && zs[2] == 2 && zs[3] == 2);
	}
	g_targetE = E;
	if (argc > 7)
	{
		// 形状を直書きで指定する(16 文字。柱 c = x + 4y の順、値は 0/1/2/4)
		const char *sp = argv[7];
		array<unsigned char, 16> a; int sum = 0;
		for (int c = 0; c < 16; c++) { a[c] = (unsigned char)(sp[c] - '0'); sum += a[c]; }
		if (sum != E) { printf("形状の E=%d が turn と合いません\n", sum); return 1; }
		g_shapes.push_back(a);
	}
	else dfs(0, 0, 0);
	printf("[turn=%d E=%d] 適格な形状数 = %zu\n", turn, E, g_shapes.size());
	if (g_shapes.empty()) return 0;

	long long valid = 0, mstarInf = 0, ok = 0, miss = 0, bad = 0;
	long long crossCnt = 0;
	int shown = 0;
	const auto t0 = chrono::steady_clock::now();

	for (long long it = 0; it < trials; it++)
	{
		setup_shape(g_shapes[rndi((int)g_shapes.size())]);
		ull B, W;
		if (!color_it(turn, B, W)) continue;
		Board b;
		const bool blackToMove = ((turn - 1) & 1) == 0;
		b.Me = blackToMove ? B : W; b.You = blackToMove ? W : B;
		if (b.turn() != turn) continue;
		if (Board::win(b.Me) == State::End || Board::win(b.You) == State::End) continue;
		const ull hand = b.valid_move();
		const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
		if ((hand & rMe) || (hand & rYou)) continue;      // 制約(C)
		if (!gate_A2(b) || !gate_T(b) || !gate_3(b)) continue;
		valid++;

		// 全空き H4 ラインの交差の有無
		{
			const ull occ = b.Me | b.You;
			int lines[10], nl = 0;
			for (int k = 0; k < 10; k++)
			{
				bool all = true;
				for (int j = 0; j < 4; j++) if (occ >> (COLSET[k][j] + 48) & 1) { all = false; break; }
				if (all) lines[nl++] = k;
			}
			bool cross = false;
			for (int i2 = 0; i2 < nl && !cross; i2++)
				for (int j2 = i2 + 1; j2 < nl && !cross; j2++)
					for (int u = 0; u < 4; u++)
						for (int v = 0; v < 4; v++)
							if (COLSET[lines[i2]][u] == COLSET[lines[j2]][v]) cross = true;
			if (cross) crossCnt++;
		}

		const int pred = ruleR2(turn, rMe, rYou);
		if (g_onlyinf && pred != 0) continue;             // m*=∞ だけを厳密解にかける(推測 1/2 の的)
		const int exact = solve(b);
		if (pred == 0) mstarInf++;
		if (pred == exact) ok++; else if (pred == 0) miss++; else bad++;

		if (pred != exact && shown < maxdump)
		{
			shown++;
			printf("\n===== 証明済ゲート G_A2 ∧ G_T ∧ G_3 を通過したのに R2 が外れた例 (%s) =====\n",
			       pred == 0 ? "取りこぼし = 推測 1/2 の反例" : "誤断定 = 定理 9 の反例");
			dump(b, B, W);
		}
	}
	const double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	printf("[turn=%d E=%d] 試行 %lld / ゲート通過 %lld (交差あり %lld) / m*=∞ %lld\n",
	       turn, E, trials, valid, crossCnt, mstarInf);
	printf("   一致 %lld  取りこぼし %lld  誤断定 %lld   (%.1f 秒, %lld ノード)\n", ok, miss, bad, sec, g_nodes);
	return 0;
}
