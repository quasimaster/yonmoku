// 「G_A2 局面の還元定理(本研究の定理 N6)」に基づく、推測 1 / 推測 2 の完全検証。
//
// 定理 N6: 制約(C) ∧ G_A2 の下で、局面の値は
//            (1) 柱の高さベクトル(形状) と (2) 空きマスに付いたリーチのラベル
//          だけで決まる。石の並びのそれ以外の情報は一切値に影響しない。
//          (系 A1 より、全ラインは「全空き(空き4)」「既存リーチ(空き1・単色)」「死んだライン」の
//           いずれかで、空き 3 のラインは補題 N1 により存在しないため。)
//
// 系 N7: さらに G_T ∧ m*=∞ ならラベルは次に限られる。
//          K(唯一の h=4 の柱)の 段2=黒 / 段3=白 / 段4=黒、その他 h=2 の柱の 段4=黒。
//
// 補題 16(ラベル単調性)より、
//    (A) 白のラベルを最大・黒を空 にして「白が勝てない」ことを示せば、全ラベル割当で白は勝てない
//    (B) 黒のラベルを最大・白を空 にして「黒が勝てない」ことを示せば、全ラベル割当で黒は勝てない
// よって 1 形状あたり 2 回の求解で、その形状に載るすべての実盤面局面を尽くせる。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o reduced_verify.exe reduced_verify.cpp
// 実行:
//   ./reduced_verify.exe check <turn> <試行> [seed]   ... 実盤面との突合(定理 N6 の検証)
//   ./reduced_verify.exe sweep <E>                    ... その E の全形状を完全検証
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;
static const ull M1 = 0x000000000000ffffuLL, M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL, M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

static ull rs = 88172645463325252uLL;
static inline ull rnd() { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (unsigned)n); }
static inline ull mix(ull x)
{ x ^= x >> 33; x *= 0xff51afd7ed558ccduLL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53uLL; return x ^ (x >> 33); }

// ==================================================================== 還元モデル
struct Reduced
{
	ull emptyMask = 0;              // 空きマス集合(形状で決まる)
	ull base = 0;                   // 既に石で埋まっているマス(= ~emptyMask)
	ull labMe = 0, labYou = 0;      // 初期ラベル(手番側 / 相手側)
	int nOpen = 0;
	ull openLine[76];               // 全空きライン
	ull relMask = 0;                // 値に影響する(= 全空きライン上の)マス
	int cellLines[64][8], cellN[64];// マス → それを含む全空きラインの番号
	ull salt = 0;                   // 置換表を局面ごとに分離するための種
	unsigned gen = 0;               // 局面世代(置換表の誤ヒットを完全に防ぐ)

	void build(const int h[16], ull labB, ull labW, bool meIsBlack)
	{
		emptyMask = 0;
		for (int c = 0; c < 16; c++)
			for (int k = 0; k < h[c]; k++) emptyMask |= 1uLL << (c + 16 * (3 - k));
		base = ~emptyMask;
		labMe = meIsBlack ? labB : labW;
		labYou = meIsBlack ? labW : labB;
		nOpen = 0; relMask = 0;
		for (int i = 0; i < LINES_NUM; i++)
			if ((LINES[i] & emptyMask) == LINES[i]) { openLine[nOpen++] = LINES[i]; relMask |= LINES[i]; }
		for (int p = 0; p < 64; p++)
		{
			cellN[p] = 0;
			for (int i = 0; i < nOpen; i++) if (openLine[i] >> p & 1) cellLines[p][cellN[p]++] = i;
		}
		// 形状もラベルも違えば同じ (filled, me) でも値が違う。置換表の衝突を防ぐ。
		static unsigned g = 0;
		gen = ++g;
		salt = emptyMask * 0x9e3779b97f4a7c15uLL + labMe * 0xbf58476d1ce4e5b9uLL + labYou * 0x94d049bb133111ebuLL;
	}
};

static Reduced R;
struct RTTE { ull k1, k2; unsigned gen; int val; };
static const int RTTBITS = 24;
static vector<RTTE> r_tt(1u << RTTBITS);
static long long r_nodes = 0;

// 手番側が p に打って即勝ちか(初期ラベル、または全空きライン上で 4 個目)
static inline bool wins_by(ull me, int p, ull labMeNow)
{
	if (labMeNow >> p & 1) return true;
	for (int i = 0; i < R.cellN[p]; i++)
	{
		const ull L = R.openLine[R.cellLines[p][i]];
		if ((me & L) == (L ^ (1uLL << p))) return true;
	}
	return false;
}

// me / you: 空き領域に置かれた石。labMe / labYou: それぞれの初期ラベル。
static int rsolve(ull me, ull you, ull labMe, ull labYou)
{
	r_nodes++;
	const ull filled = me | you | R.base;
	ull hand = ((filled << 16) | M1) & ~filled & R.emptyMask;
	if (!hand) return 0;

	// 手番側の即勝ち
	for (ull x = hand; x; x &= x - 1)
	{
		const int p = __builtin_ctzll(x);
		if (wins_by(me, p, labMe)) return +1;
	}
	// 相手の即勝ちマス(= 塞がなければ負け)
	ull danger = 0;
	for (ull x = hand; x; x &= x - 1)
	{
		const int p = __builtin_ctzll(x);
		if (wins_by(you, p, labYou)) danger |= 1uLL << p;
	}
	if (danger)
	{
		if (__builtin_popcountll(danger) > 1) return -1;
		hand = danger;
	}

	const ull k1 = filled ^ R.salt, k2 = (me & R.relMask) ^ (R.salt * 0x2545f4914f6cdd1duLL);
	const ull key = mix(k1 * 0x9e3779b97f4a7c15uLL ^ mix(k2));
	RTTE &e = r_tt[key & ((1u << RTTBITS) - 1)];
	if (e.gen == R.gen && e.k1 == k1 && e.k2 == k2) return e.val;

	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand; hand ^= bit;
		const int v = -rsolve(you, me | bit, labYou, labMe);
		if (v > best) best = v;
		if (best == 1) break;
	}
	e.k1 = k1; e.k2 = k2; e.gen = R.gen; e.val = best;
	return best;
}

// ==================================================================== 形状列挙
static int g_need[LINES_NUM][16], g_maxcol[LINES_NUM];
static bool g_isH3[LINES_NUM];
static int h[16];
static vector<array<unsigned char, 16>> g_shapes;
static int g_targetE;

static bool check_lines(int depth)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		if (g_maxcol[i] != depth) continue;
		int e = 0;
		for (int c = 0; c < 16; c++) if (g_need[i][c] && h[c] >= g_need[i][c]) e++;
		if (e == 3) return false;               // G_A2(補題 N1)
		if (g_isH3[i] && e == 4) return false;  // G_3
	}
	return true;
}
static void dfs(int c, int used4, int sum)
{
	if (sum > g_targetE) return;
	if (c == 16)
	{
		if (sum != g_targetE) return;
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
static void init_shape_tables()
{
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
}

// m*=∞ で許されるラベル集合(系 N7)
//   黒: K の段2 / K の段4 / h=2 の柱の段4     白: K の段3
static void max_labels(const int hh[16], ull &labB, ull &labW)
{
	labB = labW = 0;
	for (int c = 0; c < 16; c++)
	{
		if (hh[c] == 2) labB |= 1uLL << (c + 48);                     // 段4(埋没)
		if (hh[c] == 4) { labB |= 1uLL << (c + 16); labB |= 1uLL << (c + 48); labW |= 1uLL << (c + 32); }
	}
}

// ==================================================================== 実盤面との突合
struct TTE { ull me, you; int val; };
static vector<TTE> g_tt;   // check モードでのみ確保する
static int solve(const Board &b)
{
	ull hand = b.valid_move();
	if (!hand) return 0;
	const ull rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou) { if (__builtin_popcountll(hand & rYou) > 1) return -1; hand &= rYou; }
	const ull key = mix(b.Me * 0x9e3779b97f4a7c15uLL ^ mix(b.You));
	TTE &e = g_tt[key & ((1u << 24) - 1)];
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

static ull g_empty2, g_hand2;
static int g_ecount[LINES_NUM], g_cells[64], g_ncell;
static void setup_shape(const array<unsigned char, 16> &a)
{
	for (int c = 0; c < 16; c++) h[c] = a[c];
	g_empty2 = 0;
	for (int c = 0; c < 16; c++)
		for (int k = 0; k < h[c]; k++) g_empty2 |= 1uLL << (c + 16 * (3 - k));
	const ull occ = ~g_empty2;
	g_hand2 = (occ << 16 | M1) & ~occ;
	g_ncell = 0;
	for (int i = 0; i < 64; i++) if (!(g_empty2 >> i & 1)) g_cells[g_ncell++] = i;
	for (int i = 0; i < LINES_NUM; i++) g_ecount[i] = __builtin_popcountll(LINES[i] & g_empty2);
}
static int energy(ull B, ull W)
{
	int e = 0;
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int ec = g_ecount[i];
		if (ec >= 3) continue;
		const int cb = __builtin_popcountll(B & LINES[i]), cw = __builtin_popcountll(W & LINES[i]);
		if (ec == 0) { if (cb == 4 || cw == 4) e++; }
		else if (ec == 1) { if (cb == 3 || cw == 3) { if (LINES[i] & g_empty2 & g_hand2) e++; } }
		else { if (cb == 2 || cw == 2) e++; }
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

static int mode_check(int turn, long long trials)
{
	const int E = 65 - turn;
	g_targetE = E; dfs(0, 0, 0);
	printf("[突合 turn=%d E=%d] 形状数 %zu\n", turn, E, g_shapes.size());
	long long n = 0, diff = 0;
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
		if ((hand & rMe) || (hand & rYou)) continue;
		// 実際のラベル(埋没リーチ)を取り出して還元モデルへ
		const ull labB = (blackToMove ? rMe : rYou) & ~(b.Me | b.You);
		const ull labW = (blackToMove ? rYou : rMe) & ~(b.Me | b.You);
		R.build(h, labB, labW, blackToMove);
		const int v1 = solve(b);
		const int v2 = rsolve(0, 0, R.labMe, R.labYou);
		n++;
		if (v1 != v2)
		{
			diff++;
			if (diff <= 3) { printf("  不一致! 実盤面=%+d 還元=%+d\n", v1, v2); b.print(); }
		}
	}
	printf("[突合 turn=%d] 検査 %lld 件、不一致 %lld 件\n", turn, n, diff);
	return diff ? 1 : 0;
}

// 全空き H4 ライン(4 柱とも非満杯)の本数と、2 本が柱を共有するか
static const int COLSET0[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},
	{0,5,10,15}, {3,6,9,12},
};
static int open_h4(const int hh[16], bool &cross)
{
	int list[10], n = 0;
	for (int k = 0; k < 10; k++)
	{
		bool live = true;
		for (int j = 0; j < 4; j++) if (hh[COLSET0[k][j]] == 0) { live = false; break; }
		if (live) list[n++] = k;
	}
	cross = false;
	for (int i = 0; i < n && !cross; i++)
		for (int j = i + 1; j < n && !cross; j++)
			for (int u = 0; u < 4; u++)
				for (int v = 0; v < 4; v++)
					if (COLSET0[list[i]][u] == COLSET0[list[j]][v]) cross = true;
	return n;
}

static int g_filterX = 0;      // 1 のとき「交差する全空き H4 ラインが無い」形状だけを検証(ゲート G_X)

// ==================================================================== 全形状の完全検証
static int mode_sweep(int E, int shapeFrom, int shapeTo)
{
	g_targetE = E; dfs(0, 0, 0);
	const int turn = 65 - E;
	const bool blackToMove = ((turn - 1) & 1) == 0;
	const int lo = shapeFrom, hi = (shapeTo < 0 || shapeTo > (int)g_shapes.size()) ? (int)g_shapes.size() : shapeTo;
	printf("[完全検証 E=%d turn=%d 手番=%s] 形状 %d..%d / 全 %zu\n",
	       E, turn, blackToMove ? "黒" : "白", lo, hi, g_shapes.size());
	fflush(stdout);
	long long badW = 0, badB = 0, nShape = 0;
	long long badCross = 0, badNoCross = 0, allCross = 0;
	long long badByOpen[11] = {0}, allByOpen[11] = {0};
	const auto t0 = chrono::steady_clock::now();
	for (int s = lo; s < hi; s++)
	{
		int hh[16];
		for (int c = 0; c < 16; c++) hh[c] = g_shapes[s][c];
		bool cross = false;
		const int nOpen = open_h4(hh, cross);
		if (g_filterX == 1 && cross) continue;         // G_X1: 交差する全空き H4 ライン無し
		if (g_filterX == 2 && nOpen > 1) continue;     // G_X2: 全空き H4 ラインは高々 1 本
		nShape++;
		if (cross) allCross++;
		allByOpen[nOpen]++;
		ull mB, mW;
		max_labels(hh, mB, mW);

		// (A) 白のラベルを最大・黒を空 → 白が勝てるか
		R.build(hh, 0, mW, blackToMove);
		int vA = rsolve(0, 0, R.labMe, R.labYou);
		const bool whiteWinsA = blackToMove ? (vA < 0) : (vA > 0);
		// (B) 黒のラベルを最大・白を空 → 黒が勝てるか
		R.build(hh, mB, 0, blackToMove);
		int vB = rsolve(0, 0, R.labMe, R.labYou);
		const bool blackWinsB = blackToMove ? (vB > 0) : (vB < 0);

		if (whiteWinsA || blackWinsB)
		{
			if (whiteWinsA) badW++; else badB++;
			if (cross) badCross++; else badNoCross++;
			badByOpen[nOpen]++;
			if (badW + badB <= 5)
			{
				printf("  ★反例形状 #%d (%s が勝てる):\n", s, whiteWinsA ? "白" : "黒");
				for (int y = 3; y >= 0; y--)
				{
					printf("    ");
					for (int x = 0; x < 4; x++) printf("%d ", hh[x + 4 * y]);
					printf("\n");
				}
				fflush(stdout);
			}
		}
	}
	const double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	printf("[完全検証 E=%d filter=%d] 検証形状 %lld / 白勝ち形状 %lld / 黒勝ち形状 %lld  (%.1f 秒, %lld ノード)\n",
	       E, g_filterX, nShape, badW, badB, sec, r_nodes);
	printf("   [交差] 交差あり %lld (反例 %lld) / 交差なし %lld (反例 %lld)\n",
	       allCross, badCross, nShape - allCross, badNoCross);
	printf("   [全空き H4 ラインの本数別 反例/形状] ");
	for (int k = 0; k <= 10; k++) if (allByOpen[k]) printf("%d本:%lld/%lld ", k, badByOpen[k], allByOpen[k]);
	printf("\n");
	return (badW || badB) ? 1 : 0;
}

// 全ラベル割当を直接尽くす版(補題 16 に依存しない完全検証)
static int mode_sweepfull(int E, int shapeFrom, int shapeTo)
{
	g_targetE = E; dfs(0, 0, 0);
	const int turn = 65 - E;
	const bool blackToMove = ((turn - 1) & 1) == 0;
	const int lo = shapeFrom, hi = (shapeTo < 0 || shapeTo > (int)g_shapes.size()) ? (int)g_shapes.size() : shapeTo;
	printf("[全ラベル完全検証 E=%d turn=%d 手番=%s] 形状 %d..%d / 全 %zu\n",
	       E, turn, blackToMove ? "黒" : "白", lo, hi, g_shapes.size());
	fflush(stdout);
	long long nCase = 0, bad = 0, disagree = 0;
	const auto t0 = chrono::steady_clock::now();
	for (int s = lo; s < hi; s++)
	{
		int hh[16];
		for (int c = 0; c < 16; c++) hh[c] = g_shapes[s][c];
		// ラベルスロットを列挙(系 N7)
		int slot[32], nslot = 0, slotIsW[32];
		for (int c = 0; c < 16; c++)
		{
			if (hh[c] == 2) { slot[nslot] = c + 48; slotIsW[nslot++] = 0; }
			if (hh[c] == 4)
			{
				slot[nslot] = c + 16; slotIsW[nslot++] = 0;
				slot[nslot] = c + 32; slotIsW[nslot++] = 1;
				slot[nslot] = c + 48; slotIsW[nslot++] = 0;
			}
		}
		if (nslot > 20) { printf("  形状 #%d はスロット %d 個で打ち切り\n", s, nslot); continue; }
		// 補題 16 の近道による判定
		ull mB, mW; max_labels(hh, mB, mW);
		R.build(hh, 0, mW, blackToMove);
		const int vA = rsolve(0, 0, R.labMe, R.labYou);
		R.build(hh, mB, 0, blackToMove);
		const int vB = rsolve(0, 0, R.labMe, R.labYou);
		const bool shortcutDraw = !(blackToMove ? (vA < 0) : (vA > 0)) && !(blackToMove ? (vB > 0) : (vB < 0));

		bool allDraw = true;
		for (int m = 0; m < (1 << nslot); m++)
		{
			ull lb = 0, lw = 0;
			for (int i = 0; i < nslot; i++) if (m >> i & 1) { if (slotIsW[i]) lw |= 1uLL << slot[i]; else lb |= 1uLL << slot[i]; }
			R.build(hh, lb, lw, blackToMove);
			const int v = rsolve(0, 0, R.labMe, R.labYou);
			nCase++;
			if (v != 0)
			{
				allDraw = false; bad++;
				if (bad <= 5)
				{
					printf("  ★反例 形状 #%d ラベル %d → 値 %+d (手番=%s)\n", s, m, v, blackToMove ? "黒" : "白");
					for (int y = 3; y >= 0; y--) { printf("    "); for (int x = 0; x < 4; x++) printf("%d ", hh[x + 4 * y]); printf("\n"); }
					fflush(stdout);
				}
			}
		}
		if (allDraw != shortcutDraw) disagree++;
	}
	const double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	printf("[全ラベル完全検証 E=%d] 検査 %lld 件 / 引き分けでない %lld 件 / 近道との不一致 %lld 件 (%.1f 秒, %lld ノード)\n",
	       E, nCase, bad, disagree, sec, r_nodes);
	return bad ? 1 : 0;
}

int main(int argc, char **argv)
{
	init_lines();
	init_shape_tables();
	const string mode = argc > 1 ? argv[1] : "sweep";
	if (mode == "check")
	{
		g_tt.assign(1u << 24, TTE{0, 0, 0});
		const int turn = argc > 2 ? atoi(argv[2]) : 55;
		const long long trials = argc > 3 ? atoll(argv[3]) : 3000;
		if (argc > 4) rs = (ull)atoll(argv[4]) * 0x9e3779b97f4a7c15uLL + 12345;
		return mode_check(turn, trials);
	}
	const int E = argc > 2 ? atoi(argv[2]) : 8;
	const int from = argc > 3 ? atoi(argv[3]) : 0;
	const int to = argc > 4 ? atoi(argv[4]) : -1;
	if (mode == "sweepx") g_filterX = (argc > 5 ? atoi(argv[5]) : 1);
	if (mode == "sweepfull") return mode_sweepfull(E, from, to);
	return mode_sweep(E, from, to);
}
