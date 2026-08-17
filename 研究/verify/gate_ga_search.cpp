// G_A2 を G_A に緩められるかの検証。
//
// gate_direct_search.cpp は「空きマス 3 個のライン」を形状段階で弾いてしまう(G_A2 の幾何条件)ので、
// G_A だけを満たす局面を作れない。本プログラムはその制限を外し、
//   G_A(2石+空き2 が無い)は課すが、1石+空き3 のラインは許す
// 局面を直接構成して、各ゲートの精度を測る。
//
// 追加で測るゲート:
//   G_3   : 段3 が 4 マスとも空のラインが無い
//   G_low : 段2・段3 の「埋没」空きマスを含む生きたライン(両色を含まない・既存リーチでない)が無い
//           = 段3 以下に新しくリーチを作られる余地が無い
//   G_T0  : 高い柱(h>=3)が 0 本 = 段2 がすべて埋まっている
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o gate_ga_search.exe gate_ga_search.cpp
// 実行:   ./gate_ga_search.exe <turn> <試行回数> [seed] [mode]
//         mode 0 = 乱択形状 / mode 3 = 反例狙い(一直線 4 柱を 高さ 1,2,2,3 に固定)
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;
static const ull M1 = 0x000000000000ffffuLL, M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL, M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

static unsigned long long rs = 88172645463325252uLL;
static inline unsigned long long rnd() { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (unsigned)n); }

struct TTE { ull me, you; int val; };
static const int TTBITS = 24;
static vector<TTE> g_tt(1 << TTBITS);
static inline ull mix(ull x)
{ x ^= x >> 33; x *= 0xff51afd7ed558ccduLL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53uLL; return x ^ (x >> 33); }

static int solve(const Board &b)
{
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

static const int COLSET[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},
	{0,5,10,15}, {3,6,9,12},
};

// ------------------------------------------------------------------ ゲート群
static inline ull handmask(ull occ) { return (occ << 16 | M1) & ~occ; }

static bool gate_A(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]), cy = __builtin_popcountll(b.You & LINES[i]);
		if ((cm == 2 && cy == 0) || (cy == 2 && cm == 0)) return false;
	}
	return true;
}
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
static bool gate_H3(const Board &b)
{
	const ull occ = b.Me | b.You;
	unsigned t2 = 0;
	for (int c = 0; c < 16; c++) if (!(occ >> (c + 32) & 1)) t2 |= 1u << c;
	for (int k = 0; k < 10; k++)
	{
		unsigned m = 0;
		for (int j = 0; j < 4; j++) m |= 1u << COLSET[k][j];
		if ((t2 & m) == m) return false;
	}
	return true;
}
static int tall_count(const Board &b)
{
	const ull occ = b.Me | b.You;
	return __builtin_popcountll(~occ & M2);       // 段2 が空 = h>=3 の柱
}
static bool gate_T (const Board &b) { return tall_count(b) <= 1; }
static bool gate_T0(const Board &b) { return tall_count(b) == 0; }

// 指定マス集合のどれかに「これから新しくリーチを作られる」余地があるか
// (そのマスを含む単色ライン = 相手の石を 1 個も含まないライン で、空きマスが 2 個以上あるもの)
static bool no_creation_at(const Board &b, ull cells)
{
	if (!cells) return true;
	const ull emp = ~(b.Me | b.You);
	for (int i = 0; i < LINES_NUM; i++)
	{
		if (!(LINES[i] & cells)) continue;
		const int cm = __builtin_popcountll(b.Me & LINES[i]), cy = __builtin_popcountll(b.You & LINES[i]);
		if (cm && cy) continue;                            // 両色を含む = 死んだライン
		if (__builtin_popcountll(LINES[i] & emp) <= 1) continue;   // 空き1 = 既存リーチ / 空き0 = 決着済
		return false;
	}
	return true;
}

// G_low: 段2・段3 の埋没空きマスに新しくリーチを作られる余地が無い
static bool gate_low(const Board &b)
{
	const ull occ = b.Me | b.You;
	return no_creation_at(b, ~occ & (M2 | M3) & ~handmask(occ));
}

// G_bd: 既存の埋没リーチマス c の直下マス b_d に、新しくリーチを作られる余地が無い
//       (= 相手をテンポ手で b_d に打たせる筋を封じる)
static bool gate_bd(const Board &b)
{
	const ull occ = b.Me | b.You, emp = ~occ, hand = handmask(occ);
	const ull rB = Board::reach(b.Me) & ~b.You & emp, rW = Board::reach(b.You) & ~b.Me & emp;
	const ull buried = (rB | rW) & ~hand;
	return no_creation_at(b, (buried >> 16) & emp);        // 埋没リーチの真下のマス
}

// G_C: 今すぐ即置可能なマスに 1 手でリーチを作れるライン(2石+空き2 でその 1 つが即置可能)が無い
static bool gate_C(const Board &b)
{
	const ull occ = b.Me | b.You, hand = handmask(occ);
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]), cy = __builtin_popcountll(b.You & LINES[i]);
		if (!((cm == 2 && cy == 0) || (cy == 2 && cm == 0))) continue;
		if (LINES[i] & ~occ & hand) return false;
	}
	return true;
}

// ------------------------------------------------------------------ 局面構成
static int h[16];
static ull g_empty, g_hand;
static int g_ecount[LINES_NUM];
static int g_cells[64], g_ncell;
static int g_mode = 0;

static bool make_shape(int E)
{
	for (int c = 0; c < 16; c++) h[c] = 0;
	int rest = E;
	if (g_mode == 3)
	{
		// 反例狙い: 一直線に並ぶ 4 柱を 高さ 1 / 2 / 2 / 3 にする。
		// 高さ 3 の柱(= K)の段3 が、H3 ライン(1石+空き3)のリーチマス候補になる。
		if (E < 8) return false;
		const int *s = COLSET[rndi(10)];
		const int kk = rndi(4);
		int order[4] = {1, 2, 2, 3};
		{ const int t = order[3]; order[3] = order[kk]; order[kk] = t; }
		for (int j = 0; j < 4; j++) h[s[j]] = order[j];
		rest = E - 8;
	}
	else if (g_mode != 4 && rndi(3) != 0)
	{
		const int ht = 3 + rndi(2);
		if (ht <= rest) { h[rndi(16)] = ht; rest -= ht; }
	}
	int guard = 0;
	while (rest > 0)
	{
		if (++guard > 10000) return false;
		const int c = rndi(16);
		// mode 4 は高さ制限なし(高い柱を何本でも作る)。それ以外は G_T を満たす形状に限る。
		if (h[c] >= (g_mode == 4 ? 4 : 2)) continue;
		h[c]++; rest--;
	}
	g_empty = 0;
	for (int c = 0; c < 16; c++)
		for (int k = 0; k < h[c]; k++) g_empty |= 1uLL << (c + 16 * (3 - k));
	const ull occ = ~g_empty;
	g_hand = handmask(occ);
	g_ncell = 0;
	for (int i = 0; i < 64; i++) if (!(g_empty >> i & 1)) g_cells[g_ncell++] = i;
	for (int i = 0; i < LINES_NUM; i++) g_ecount[i] = __builtin_popcountll(LINES[i] & g_empty);
	return true;
}

// G_A2 は課さない。ec == 3 のラインは許す。
// g_strict = 1 のときだけ ec == 2 の単色(= G_A 違反)も禁止する。
static int g_strict = 0;
static int energy(ull B, ull W)
{
	int e = 0;
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int ec = g_ecount[i];
		if (ec >= 3) continue;
		const int cb = __builtin_popcountll(B & LINES[i]), cw = __builtin_popcountll(W & LINES[i]);
		if (ec == 0) { if (cb == 4 || cw == 4) e++; }
		else if (ec == 1)
		{
			if (!(LINES[i] & g_empty & g_hand)) continue;
			if (cb == 3 || cw == 3) e++;                  // 制約(C) 違反
		}
		else if (g_strict) { if (cb == 2 || cw == 2) e++; }   // G_A 違反
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
	for (int step = 0; step < 20000 && cur > 0; step++)
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
	for (int trial = 0; trial < 4000; trial++)
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

static void dump(const Board &b)
{
	const int turn = b.turn();
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const ull rB = (now == Color::Black) ? rMe : rYou, rW = (now == Color::Black) ? rYou : rMe;
	const ull occ = b.Me | b.You, hand = b.valid_move();
	printf("  turn=%d(手番=%s) 厳密解=%+d R2=%+d | G_A=%d G_A2=%d G_T=%d G_T0=%d G_3=%d G_low=%d\n",
	       turn, now == Color::Black ? "黒" : "白", solve(b), ruleR2(turn, rMe, rYou),
	       gate_A(b), gate_A2(b), gate_T(b), gate_T0(b), gate_H3(b), gate_low(b));
	b.print();
	printf("  空きマス:");
	for (int i = 0; i < 64; i++) if (!(occ >> i & 1))
		printf("  (x%d,y%d,段%d)%s%s%s", X(i) + 1, Y(i) + 1, Z(i) + 1,
		       (hand >> i & 1) ? "[即置可]" : "", (rB >> i & 1) ? "[黒リーチ]" : "", (rW >> i & 1) ? "[白リーチ]" : "");
	printf("\n  最善手順:");
	Board cur = b;
	for (int ply = 0; ply < 24; ply++)
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
}

struct Stat { long long n = 0, ok = 0, miss = 0, bad = 0, bwin = 0; };
static int g_turn_now = 0;
static long long g_h4lines = 0, g_h4multi = 0, g_h4cross = 0;
static void add(Stat &s, int pred, int exact)
{
	s.n++;
	if (pred == exact) s.ok++; else if (pred == 0) s.miss++; else s.bad++;
	// 黒の勝ちか(exact は手番視点。手番は turn が奇数なら黒)
	const bool blackToMove = ((g_turn_now - 1) & 1) == 0;
	if (( blackToMove && exact > 0) || (!blackToMove && exact < 0)) s.bwin++;
}

int main(int argc, char **argv)
{
	init_lines();
	const int turn = argc > 1 ? atoi(argv[1]) : 57;
	const long long trials = argc > 2 ? atoll(argv[2]) : 200000;
	if (argc > 3) rs = (ull)atoll(argv[3]) * 0x9e3779b97f4a7c15uLL + 12345;
	if (argc > 4) g_mode = atoi(argv[4]);
	const int E = 65 - turn;

	if (argc > 5) g_strict = atoi(argv[5]);
	g_turn_now = turn;

	long long valid = 0;
	Stat sA, sAT3, sAT3L, sA2T3, sT0, sT0bd, sT0bdC, sTbd, sTbd3L, sTbd3LC;
	Stat byTall[5], byN4[5], byC[17];      // 高い柱の本数 / 全空き柱(h=4)の本数 / 空きのある柱の本数
	Stat sT0A2, sT0C;
	int shown = 0;

	for (long long it = 0; it < trials; it++)
	{
		if (!make_shape(E)) continue;
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
		valid++;

		const bool a = gate_A(b), a2 = gate_A2(b), t = gate_T(b), t0 = gate_T0(b);
		const bool g3 = gate_H3(b), lo = gate_low(b), bd = gate_bd(b), gc = gate_C(b);
		const int exact = solve(b), pred = ruleR2(turn, rMe, rYou);

		if (a && t && bd)               add(sA,      pred, exact);   // G_A ∧ G_T ∧ G_bd
		if (a && t && g3 && bd)         add(sTbd,    pred, exact);   // G_A ∧ G_T ∧ G_3 ∧ G_bd
		if (a && t && g3 && bd && gc)   add(sT0,     pred, exact);   // 上 ∧ G_C
		if (a && t && g3)               add(sAT3,    pred, exact);
		if (a && t && g3 && lo)         add(sAT3L,   pred, exact);
		if (a2 && t && g3)              add(sA2T3,   pred, exact);
		if (t0)                         add(sT0bd,   pred, exact);
		if (t0 && bd)                   add(sT0bdC,  pred, exact);
		if (t0 && bd && gc)             add(sTbd3L,  pred, exact);
		if (a2 && t && bd)              add(sTbd3LC, pred, exact);
		if (t0 && a2)                   add(sT0A2,   pred, exact);
		if (t0 && gc)                   add(sT0C,    pred, exact);

		if (a2 && t && g3)
		{
			// 定理C1 の証明の穴の検査:
			// 「全空きの H4 ライン」が 2 本以上あって、しかも柱を共有しているか。
			// 共有していれば、攻撃側の 1 手が 2 本のラインに同時に石を置けるので
			// 「守備側は 1 手で消火できる」という議論が崩れる。
			const ull occ = b.Me | b.You;
			int lines[10], nl = 0;
			for (int k = 0; k < 10; k++)
			{
				ull m = 0;
				for (int j = 0; j < 4; j++) m |= 1uLL << (COLSET[k][j] + 48);   // 段4 = z=3
				if (!(occ & m)) lines[nl++] = k;
			}
			g_h4lines += nl;
			if (nl >= 2) g_h4multi++;
			bool cross = false;
			for (int i2 = 0; i2 < nl && !cross; i2++)
				for (int j2 = i2 + 1; j2 < nl && !cross; j2++)
					for (int u = 0; u < 4; u++)
						for (int v = 0; v < 4; v++)
							if (COLSET[lines[i2]][u] == COLSET[lines[j2]][v]) cross = true;
			if (cross) g_h4cross++;
		}

		{	// 柱形状による層別
			const ull occ = b.Me | b.You;
			int n4 = 0, nz = 0;
			for (int c = 0; c < 16; c++)
			{
				int e = 0;
				for (int z = 0; z < 4; z++) if (!(occ >> (c + 16 * z) & 1)) e++;
				if (e == 4) n4++;
				if (e >= 1) nz++;
			}
			const int tl = tall_count(b);
			add(byTall[tl < 4 ? tl : 4], pred, exact);
			add(byN4  [n4 < 4 ? n4 : 4], pred, exact);
			add(byC   [nz < 17 ? nz : 16], pred, exact);
		}

		if (a && t && g3 && bd && pred != exact && shown < 2)
		{
			shown++;
			printf("\n===== G_A ∧ G_T ∧ G_3 ∧ G_bd を通過したのに R2 が外れた例 (%s) =====\n",
			       pred == 0 ? "取りこぼし" : "誤断定");
			dump(b);
			printf("  到達可能(交互着手+重力): %s\n", reachable(B, W) ? "YES" : "判定できず");
			fflush(stdout);
		}
	}

	printf("\n[turn=%d (E=%d) mode=%d strict=%d]  試行 %lld / 制約(C)込みで有効 %lld\n",
	       turn, E, g_mode, g_strict, trials, valid);
	printf("  %-30s %10s %8s %10s %8s %8s\n", "ゲート", "対象数", "通過率", "取りこぼし", "誤断定", "一致");
	struct { const char *nm; Stat *s; } tbl[] = {
		{"G_A2 ∧ G_T ∧ G_3 (証明済)",    &sA2T3},
		{"G_A ∧ G_T ∧ G_3",              &sAT3},
		{"G_A ∧ G_T ∧ G_3 ∧ G_low",      &sAT3L},
		{"G_A ∧ G_T ∧ G_bd",             &sA},
		{"G_A ∧ G_T ∧ G_3 ∧ G_bd",       &sTbd},
		{"G_A ∧ G_T ∧ G_3 ∧ G_bd ∧ G_C", &sT0},
		{"G_A2 ∧ G_T ∧ G_bd (G_3 無し)", &sTbd3LC},
		{"G_T0",                         &sT0bd},
		{"G_T0 ∧ G_bd",                  &sT0bdC},
		{"G_T0 ∧ G_bd ∧ G_C",            &sTbd3L},
	};
	for (auto &r : tbl)
		printf("  %-30s %10lld %7.2f%% %10lld %8lld %8lld\n", r.nm, r.s->n,
		       valid ? 100.0 * r.s->n / valid : 0.0, r.s->miss, r.s->bad, r.s->ok);

	printf("\n  [定理C1 の穴] G_A2∧G_T∧G_3 通過局面での全空き H4 ライン:"
	       " 総数 %lld / 2 本以上 %lld 局面 / 柱を共有 %lld 局面\n",
	       g_h4lines, g_h4multi, g_h4cross);

	printf("\n  [平坦盤で黒が勝つか] 黒勝ち局面数 / 対象数\n");
	struct { const char *nm; Stat *s; } tb2[] = {
		{"G_T0",              &sT0bd},  {"G_T0 ∧ G_bd",   &sT0bdC},
		{"G_T0 ∧ G_C",        &sT0C},   {"G_T0 ∧ G_bd ∧ G_C", &sTbd3L},
		{"G_T0 ∧ G_A2",       &sT0A2},
	};
	for (auto &r : tb2)
		printf("  %-24s 黒勝ち %8lld / %8lld  (取りこぼし %lld 誤断定 %lld)\n",
		       r.nm, r.s->bwin, r.s->n, r.s->miss, r.s->bad);

	printf("\n  [層別] 高い柱(h>=3)の本数\n");
	for (int k = 0; k <= 4; k++) if (byTall[k].n)
		printf("    tall=%s : %9lld 件  取りこぼし %8lld  誤断定 %8lld  (黒勝ち %lld)\n",
		       k == 4 ? "4+" : (k == 0 ? "0 " : (k == 1 ? "1 " : (k == 2 ? "2 " : "3 "))),
		       byTall[k].n, byTall[k].miss, byTall[k].bad, byTall[k].bwin);
	printf("  [層別] 全て空きの柱(h=4)の本数\n");
	for (int k = 0; k <= 4; k++) if (byN4[k].n)
		printf("    n4=%s : %9lld 件  取りこぼし %8lld  誤断定 %8lld  (黒勝ち %lld)\n",
		       k == 4 ? "4+" : (k == 0 ? "0 " : (k == 1 ? "1 " : (k == 2 ? "2 " : "3 "))),
		       byN4[k].n, byN4[k].miss, byN4[k].bad, byN4[k].bwin);
	printf("  [層別] 空きマスを持つ柱の本数 C\n");
	for (int k = 0; k <= 16; k++) if (byC[k].n)
		printf("    C=%2d : %9lld 件  取りこぼし %8lld  誤断定 %8lld  (黒勝ち %lld)\n",
		       k, byC[k].n, byC[k].miss, byC[k].bad, byC[k].bwin);
	return 0;
}
