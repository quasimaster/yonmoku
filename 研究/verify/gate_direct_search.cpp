// ゲート G_A2 / G_A2∧G_T の下で段パリティ規則 R2 が厳密かどうかを、
// ランダムプレイアウトではなく「局面を直接構成する」ことで検証する。
//
// gate_verify.cpp のプレイアウト標本は turn <= 57 では G_A2 通過が年に数件しか出ず、
// 「全標本で誤り 0」という実測は標本の薄さに由来する可能性がある。
// そこで G_A2 ∧ G_T を満たす局面そのものを直接サンプリングして反例を探す。
//
// 構成手順:
//   1) 柱の高さ h[16] を乱択 (sum = E, h<=4, h>=3 の柱は高々 1 本 = G_T)
//   2) 空きマス集合の幾何チェック: 「ちょうど 3 マス空き」のラインが無いこと
//      (G_A2 ⟺ 空き3のラインが無い ∧ 空き2のラインの 2 石が異色 なので、前半は幾何だけで決まる)
//   3) 石の色を焼きなましで決定:
//        空き0 のライン → 単色4 禁止(既に決着している局面は除外)
//        空き1 かつ そのマスが即置可能 → 単色3 禁止 (制約C)
//        空き2 のライン → 2 石が同色なら禁止 (G_A2 / G_A)
//        空き3 のライン → 禁止(2 で排除済み)
//      石数は 黒 = ceil((t-1)/2), 白 = floor((t-1)/2)
//   4) 厳密解と R2 を比較。不一致なら局面と最善手順を出力し、到達可能性も判定する。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o gate_direct_search.exe gate_direct_search.cpp
// 実行:   ./gate_direct_search.exe <turn> <試行回数> [seed]
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;

static const ull M1 = 0x000000000000ffffuLL;
static const ull M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL;
static const ull M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

// ---------------------------------------------------------------- 乱数
static unsigned long long rs = 88172645463325252uLL;
static inline unsigned long long rnd()
{
	rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static inline int rndi(int n) { return (int)(rnd() % (unsigned)n); }

// ---------------------------------------------------------------- 置換表つき厳密解
struct TTE { ull me, you; int val; };
static const int TTBITS = 24;
static vector<TTE> g_tt(1 << TTBITS);

static inline ull mix(ull x)
{
	x ^= x >> 33; x *= 0xff51afd7ed558ccduLL;
	x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53uLL;
	return x ^ (x >> 33);
}

static int solve(const Board &b)
{
	ull hand = b.valid_move();
	if (!hand) return 0;
	const ull rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou)
	{
		if (__builtin_popcountll(hand & rYou) > 1) return -1;
		hand &= rYou;
	}
	const ull key = mix(b.Me * 0x9e3779b97f4a7c15uLL ^ mix(b.You));
	TTE &e = g_tt[key & ((1u << TTBITS) - 1)];
	if (e.me == b.Me && e.you == b.You) return e.val;

	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand;
		hand ^= bit;
		const int v = -solve(b.place_fast_clone(bit));
		if (v > best) best = v;
		if (best == 1) break;
	}
	e.me = b.Me; e.you = b.You; e.val = best;
	return best;
}

// ---------------------------------------------------------------- 規則 R2(低段優先)
static int ruleR2(int turn, ull rMe, ull rYou)
{
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rB = (now == Color::Black) ? rMe : rYou;
	const ull rW = (now == Color::Black) ? rYou : rMe;
	for (int m = 1; m <= 4; m++)
	{
		if ((m & 1) && (rB & MASK[m])) return now == Color::Black ? +1 : -1;
		if (!(m & 1) && (rW & MASK[m])) return now == Color::White ? +1 : -1;
	}
	return 0;
}

// 4 本が一直線に並ぶ柱の組(x-y 平面の 4 行 + 4 列 + 2 対角 = 10 組)
static const int COLSET[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},          // y 固定(x 方向)
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},          // x 固定(y 方向)
	{0,5,10,15}, {3,6,9,12},                                    // 対角
};

// ---------------------------------------------------------------- ゲート
static bool gate_A(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if ((cm == 2 && cy == 0) || (cy == 2 && cm == 0)) return false;
	}
	return true;
}
static bool gate_A2(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if (cy == 0 && (cm == 1 || cm == 2)) return false;
		if (cm == 0 && (cy == 1 || cy == 2)) return false;
	}
	return true;
}
// G_3: 「段3 が 4 マスとも空のライン(= H3 全空きライン)」が存在しない
// ⟺ 高さ2 以上の柱の集合が x-y 平面の直線 4 本組を含まない
static bool gate_H3(const Board &b)
{
	const ull occ = b.Me | b.You;
	unsigned tall2 = 0;                       // 段3 が空 = h>=2 の柱
	for (int c = 0; c < 16; c++) if (!(occ >> (c + 32) & 1)) tall2 |= 1u << c;
	for (int k = 0; k < 10; k++)
	{
		unsigned m = 0;
		for (int j = 0; j < 4; j++) m |= 1u << COLSET[k][j];
		if ((tall2 & m) == m) return false;
	}
	return true;
}

static bool gate_T(const Board &b)
{
	const ull occ = b.Me | b.You;
	int tall = 0;
	for (int c = 0; c < 16; c++)
	{
		int e = 0;
		for (int z = 0; z < 4; z++) if (!(occ >> (c + 16 * z) & 1)) e++;
		if (e >= 3) tall++;
	}
	return tall <= 1;
}

// ---------------------------------------------------------------- 局面構成
static int h[16];                 // 各柱の空きマス数
static ull g_empty, g_hand;       // 空きマス / 即置可能マス
static int g_ecount[LINES_NUM];   // 各ラインの空きマス数
static int g_cells[64], g_ncell;  // 石を置くマスの一覧

// 高さベクトルを乱択して幾何条件(空き3のラインが無い)まで確認する
// mode 1: 一直線に並ぶ 4 本の柱を高さ 2 にする(段3 の全空きライン = H3 を強制的に作る)
static int g_mode = 0;
static bool locked[16];
static bool make_shape(int E)
{
	for (int c = 0; c < 16; c++) { h[c] = 0; locked[c] = false; }
	int rest = E;
	if (g_mode == 1)
	{
		if (E < 8) return false;
		const int *s = COLSET[rndi(10)];
		for (int k = 0; k < 4; k++) h[s[k]] = 2;
		rest = E - 8;
	}
	else if (g_mode == 2)
	{
		// 一直線に並ぶ 4 本を高さ 1,1,1,2 に固定する(段4 の全空きライン = H4 だけを作り、
		// H3 が生じないようこの 4 本は以後増やさない)
		if (E < 5) return false;
		const int *s = COLSET[rndi(10)];
		const int deep = rndi(4);
		for (int k = 0; k < 4; k++) { h[s[k]] = (k == deep) ? 2 : 1; locked[s[k]] = true; }
		rest = E - 5;
	}
	// 高い柱(h>=3)は G_T より高々 1 本
	else if (rndi(3) != 0)
	{
		const int ht = 3 + rndi(2);
		if (ht <= rest) { h[rndi(16)] = ht; rest -= ht; }
	}
	int guard = 0;
	while (rest > 0)
	{
		if (++guard > 10000) return false;
		const int c = rndi(16);
		if (locked[c] || h[c] >= 2) continue;   // 高い柱は既に確定済みなので他は 2 まで
		h[c]++; rest--;
	}

	g_empty = 0;
	for (int c = 0; c < 16; c++)
		for (int k = 0; k < h[c]; k++) g_empty |= 1uLL << (c + 16 * (3 - k));
	const ull occ = ~g_empty;
	g_hand = (occ << 16 | M1) & ~occ;

	g_ncell = 0;
	for (int i = 0; i < 64; i++) if (!(g_empty >> i & 1)) g_cells[g_ncell++] = i;

	for (int i = 0; i < LINES_NUM; i++)
	{
		g_ecount[i] = __builtin_popcountll(LINES[i] & g_empty);
		if (g_ecount[i] == 3) return false;   // G_A2 に反する幾何
	}
	return true;
}

// 色割当のエネルギー(違反本数)
static int energy(ull B, ull W)
{
	int e = 0;
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int ec = g_ecount[i];
		if (ec >= 3) continue;
		const int cb = __builtin_popcountll(B & LINES[i]);
		const int cw = __builtin_popcountll(W & LINES[i]);
		if (ec == 0) { if (cb == 4 || cw == 4) e++; }           // 既に決着している → 除外
		else if (ec == 1)
		{
			if (!(LINES[i] & g_empty & g_hand)) continue;       // 埋没マスの単色3(=リーチ)は許す
			if (cb == 3 || cw == 3) e++;                        // 制約(C) 違反
		}
		else /* ec == 2 */ { if (cb == 2 || cw == 2) e++; }     // G_A2 / G_A 違反
	}
	return e;
}

// 焼きなましで制約を満たす色割当を探す
static bool color_it(int turn, ull &B, ull &W)
{
	const int stones = turn - 1;
	const int nb = (stones + 1) / 2;     // 黒石数
	if (g_ncell != stones) return false;

	int idx[64];
	for (int i = 0; i < g_ncell; i++) idx[i] = i;
	for (int i = g_ncell - 1; i > 0; i--) { const int j = rndi(i + 1); const int t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
	B = W = 0;
	for (int i = 0; i < g_ncell; i++)
		(i < nb ? B : W) |= 1uLL << g_cells[idx[i]];

	int cur = energy(B, W);
	for (int step = 0; step < 20000 && cur > 0; step++)
	{
		// 黒石 1 個と白石 1 個を交換(石数を保つ)
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

// ---------------------------------------------------------------- 到達可能性(交互着手 + 重力)
static bool reachable(ull B, ull W)
{
	const int stones = __builtin_popcountll(B | W);
	for (int trial = 0; trial < 2000; trial++)
	{
		int fill[16] = {0};
		bool ok = true;
		for (int k = 0; k < stones; k++)
		{
			const bool wantBlack = ((k & 1) == 0);
			int cand[16], nc = 0;
			for (int c = 0; c < 16; c++)
			{
				if (fill[c] >= 4 - h[c]) continue;
				const int i = c + 16 * fill[c];
				const bool isB = (B >> i & 1) != 0;
				if (isB == wantBlack) cand[nc++] = c;
			}
			if (!nc) { ok = false; break; }
			fill[cand[rndi(nc)]]++;
		}
		if (ok) return true;
	}
	return false;
}

// ---------------------------------------------------------------- 出力
static void dump(const Board &b)
{
	const int turn = b.turn();
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const ull rB = (now == Color::Black) ? rMe : rYou, rW = (now == Color::Black) ? rYou : rMe;
	const ull occ = b.Me | b.You, hand = b.valid_move();
	printf("  turn=%d(手番=%s) 厳密解=%+d R2=%+d  G_A=%d G_A2=%d G_T=%d\n", turn,
	       now == Color::Black ? "黒" : "白", solve(b), ruleR2(turn, rMe, rYou),
	       gate_A(b), gate_A2(b), gate_T(b));
	b.print();
	printf("  空きマス:");
	for (int i = 0; i < 64; i++) if (!(occ >> i & 1))
		printf("  (x%d,y%d,段%d)%s%s%s", X(i) + 1, Y(i) + 1, Z(i) + 1,
		       (hand >> i & 1) ? "[即置可]" : "", (rB >> i & 1) ? "[黒リーチ]" : "", (rW >> i & 1) ? "[白リーチ]" : "");
	printf("\n  最善手順:");
	Board cur = b;
	for (int ply = 0; ply < 20; ply++)
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

	// 根と、その最善手を指した直後の、全合法手の値(手を指した側から見た値)を並べる。
	// 「なぜ相手は自分の脅威を手放さざるを得ないのか」を確かめるため。
	Board pos = b;
	for (int depth = 0; depth < 2; depth++)
	{
		const ull hh = pos.valid_move();
		if (!hh) break;
		const char *who = ((pos.turn() - 1) & 1) ? "白" : "黒";
		printf("  %s手番(turn=%d)の全合法手の値:", who, pos.turn());
		int best = -2; ull bb = 0;
		for (ull x = hh; x; x &= x - 1)
		{
			const ull bit = x & -x;
			const int v = -solve(pos.place_fast_clone(bit));
			const int i = __builtin_ctzll(bit);
			printf("  (x%d,y%d,段%d)=%+d", X(i) + 1, Y(i) + 1, Z(i) + 1, v);
			if (v > best) { best = v; bb = bit; }
		}
		printf("\n");
		pos = pos.place_fast_clone(bb);
	}
}

int main(int argc, char **argv)
{
	init_lines();
	const int turn = argc > 1 ? atoi(argv[1]) : 58;
	const long long trials = argc > 2 ? atoll(argv[2]) : 100000;
	if (argc > 3) rs = (ull)atoll(argv[3]) * 0x9e3779b97f4a7c15uLL + 12345;
	if (argc > 4) g_mode = atoi(argv[4]);
	const int E = 65 - turn;

	long long shape_ok = 0, colored = 0, valid = 0;
	long long nA = 0, nA2 = 0, nA2T = 0;
	long long okA = 0, missA = 0, badA = 0;
	long long okA2 = 0, missA2 = 0, badA2 = 0;
	long long okA2T = 0, missA2T = 0, badA2T = 0;
	long long nA2TH = 0, okA2TH = 0, missA2TH = 0, badA2TH = 0;
	int shown = 0;

	for (long long it = 0; it < trials; it++)
	{
		if (!make_shape(E)) continue;
		shape_ok++;
		ull B, W;
		if (!color_it(turn, B, W)) continue;
		colored++;

		Board b;
		const bool blackToMove = ((turn - 1) & 1) == 0;
		b.Me = blackToMove ? B : W;
		b.You = blackToMove ? W : B;
		if (b.turn() != turn) continue;
		if (Board::win(b.Me) == State::End || Board::win(b.You) == State::End) continue;
		const ull hand = b.valid_move();
		const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
		if ((hand & rMe) || (hand & rYou)) continue;    // 制約(C)
		valid++;

		const bool a = gate_A(b), a2 = gate_A2(b), t = gate_T(b);
		if (!a) continue;                                // G_A すら通らない局面は対象外
		const int exact = solve(b), pred = ruleR2(turn, rMe, rYou);

		nA++;
		if (pred == exact) okA++; else if (pred == 0) missA++; else badA++;
		if (a2) { nA2++; if (pred == exact) okA2++; else if (pred == 0) missA2++; else badA2++; }
		if (a2 && t && gate_H3(b))
		{
			nA2TH++;
			if (pred == exact) okA2TH++; else if (pred == 0) missA2TH++; else badA2TH++;
		}
		if (a2 && t)
		{
			nA2T++;
			if (pred == exact) okA2T++;
			else
			{
				if (pred == 0) missA2T++; else badA2T++;
				if (shown < 3)
				{
					shown++;
					printf("\n===== G_A2 ∧ G_T を通過したのに R2 が外れた例 (%s) =====\n",
					       pred == 0 ? "取りこぼし" : "誤断定");
					dump(b);
					printf("  到達可能(交互着手+重力): %s\n", reachable(B, W) ? "YES" : "判定できず");
					fflush(stdout);
				}
			}
		}
	}

	printf("\n[turn=%d (E=%d) 直接構成サーチ]  試行 %lld\n", turn, E, trials);
	printf("  形状通過(空き3ライン無し) : %lld\n", shape_ok);
	printf("  彩色成功                   : %lld\n", colored);
	printf("  制約(C)込みで有効な局面     : %lld\n", valid);
	printf("  %-14s %10s %10s %10s %10s\n", "ゲート", "対象数", "一致", "取りこぼし", "誤断定");
	printf("  %-14s %10lld %10lld %10lld %10lld\n", "G_A",     nA,   okA,   missA,   badA);
	printf("  %-14s %10lld %10lld %10lld %10lld\n", "G_A2",    nA2,  okA2,  missA2,  badA2);
	printf("  %-14s %10lld %10lld %10lld %10lld\n", "G_A2∧G_T", nA2T, okA2T, missA2T, badA2T);
	printf("  %-14s %10lld %10lld %10lld %10lld\n", "G_A2∧G_T∧G_3", nA2TH, okA2TH, missA2TH, badA2TH);
	return 0;
}
