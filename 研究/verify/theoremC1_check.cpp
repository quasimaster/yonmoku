// 定理 C1 の機械検証。
//
// `研究\最終盤評価関数_turn57以下の証明.md` 定理 C1 は
//   「G_A2 ∧ G_T ∧ G_3 の下では、どちらの色も『根で全空きだったライン』の上にリーチを作れない」
// と主張するが、証明には穴がある(攻撃側の 1 手が最大 3 本の H4 ラインを同時に伸ばす)。
// そこで結論そのものを直接ゲーム木で判定する。
//
// 補助ゲーム: 攻撃側 atk は「根で全空きだったライン L に atk の石 3 個以上 + 相手の石 0」を作れば成功。
//   ・攻撃側は自由に打てる(相手の脅威を阻止する義務も課さない = 攻撃側に有利な側に倒す)
//   ・守備側は自由に打てるが、攻撃側が即置可能マスにリーチを持つときは阻止に強制される
//     (2 個以上あれば止められないので攻撃側の成功とみなす)
//   ・盤が埋まるまで成功しなければ守備側の勝ち
// 「全局面で守備側が防ぎきる」なら 定理 C1 の結論は正しい。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o theoremC1_check.exe theoremC1_check.cpp
// 実行:   ./theoremC1_check.exe <turn> <試行回数> [seed]
#include "../../code/common.hpp"
#include "../../code/board.hpp"
#include <unordered_map>

typedef unsigned long long ull;
static const ull M1 = 0x000000000000ffffuLL, M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL;

static unsigned long long rs = 88172645463325252uLL;
static inline unsigned long long rnd() { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (unsigned)n); }
static inline ull handmask(ull occ) { return (occ << 16 | M1) & ~occ; }

static const int COLSET[10][4] = {
	{0,1,2,3}, {4,5,6,7}, {8,9,10,11}, {12,13,14,15},
	{0,4,8,12}, {1,5,9,13}, {2,6,10,14}, {3,7,11,15},
	{0,5,10,15}, {3,6,9,12},
};

// ---------------------------------------------------------------- ゲート
static bool gate_A2(ull B, ull W)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cb = __builtin_popcountll(B & LINES[i]), cw = __builtin_popcountll(W & LINES[i]);
		if (cw == 0 && (cb == 1 || cb == 2)) return false;
		if (cb == 0 && (cw == 1 || cw == 2)) return false;
	}
	return true;
}
static bool gate_T(ull occ) { return __builtin_popcountll(~occ & M2) <= 1; }
static bool gate_H3(ull occ)
{
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

// ---------------------------------------------------------------- 補助ゲーム
static vector<ull> g_open;          // 根で 4 マスとも空だったライン
static ull g_atkAll, g_defAll;      // 攻撃側 / 守備側の色(0=黒 なら B が攻撃)
static int g_atkIsBlack;
static int g_realistic = 0;
static int g_forceDraw = 0;
static int g_defStrategy = 0;

// g_strictSuccess = 0: 「根の全空きライン上に 3 石」で成功(定理 C1 の主張どおり)
//                  = 1: さらに「残る空きマスが埋没している」ことを要求(= 有害な創出だけを数える)
static int g_strictSuccess = 0;
static inline bool success(ull atk, ull def)
{
	const ull occ = atk | def, hand = handmask(occ);
	if (g_strictSuccess == 2)
	{
		// 二重脅威: 即置可能マス上に攻撃側のリーチが 2 個以上
		const ull r = Board::reach(atk) & ~def & ~occ & hand;
		return __builtin_popcountll(r) >= 2;
	}
	for (ull L : g_open)
	{
		if (def & L) continue;
		const int c = __builtin_popcountll(atk & L);
		if (c < 3) continue;
		if (!g_strictSuccess) return true;
		if (c == 4) return true;                              // 既に 4 個並び
		if ((L & ~occ) & ~hand) return true;                  // 残る空きマスが埋没 = 有害
	}
	return false;
}

struct Key { ull b, w; };
struct KeyHash { size_t operator()(const pair<ull,ull>&k) const
	{ return (size_t)(k.first * 0x9e3779b97f4a7c15uLL ^ (k.second + 0x165667b19e3779f9uLL)); } };
static unordered_map<pair<ull,ull>, char, KeyHash> g_memo;

// 攻撃側が成功できるなら true
static bool aux(ull B, ull W)
{
	const ull occ = B | W;
	const ull hand = handmask(occ);
	if (!hand) return false;                                  // 盤が埋まった → 守備側の勝ち
	auto it = g_memo.find({B, W});
	if (it != g_memo.end()) return it->second != 0;

	const int turn = __builtin_popcountll(occ) + 1;
	const bool blackToMove = (turn & 1) != 0;
	const bool atkToMove = (blackToMove == (g_atkIsBlack != 0));
	const ull atk = g_atkIsBlack ? B : W, def = g_atkIsBlack ? W : B;

	bool res;
	if (atkToMove)
	{
		// 現実的モデル: 攻撃側も守備側の即リーチには阻止を強制される
		ull moves = hand;
		if (g_realistic)
		{
			const ull rDef = Board::reach(def) & ~atk & ~occ;
			const ull forced = rDef & hand;
			if (__builtin_popcountll(forced) >= 2) { g_memo[{B, W}] = 0; return false; }  // 攻撃側が負ける
			if (forced) moves = forced;
		}
		res = false;
		for (ull x = moves; x && !res; x &= x - 1)
		{
			const ull bit = x & -x;
			const ull atk2 = atk | bit;
			if (success(atk2, def)) { res = true; break; }
			res = g_atkIsBlack ? aux(B | bit, W) : aux(B, W | bit);
		}
	}
	else
	{
		// 攻撃側が即置可能マスにリーチを持つなら守備側は阻止に強制される
		const ull rAtk = Board::reach(atk) & ~def & ~occ;
		const ull forced = rAtk & hand;
		if (__builtin_popcountll(forced) >= 2) { g_memo[{B, W}] = 1; return true; }
		ull moves = forced ? forced : hand;
		if (!forced && g_defStrategy)
		{
			// 補題 Z5 の検証: 守備側を「交点優先の消火」に固定する。
			//   危険ライン = 根の全空きラインのうち守備側の石を含まず攻撃側の石を含むもの
			//   候補マス   = 危険ライン上の即置可能な空きマス
			//   選択基準   = 乗っている危険ラインの本数(= 交点度)が最大、同点なら攻撃側の石数の合計が最大
			ull best = 0; int bestKey = -1;
			for (ull x = hand; x; x &= x - 1)
			{
				const ull bit = x & -x;
				int deg = 0, adv = 0;
				for (ull L : g_open)
				{
					if (!(L & bit) || (def & L)) continue;
					const int c = __builtin_popcountll(atk & L);
					if (c == 0) continue;
					deg++; adv += c;
				}
				if (!deg) continue;
				const int key = deg * 100 + adv;
				if (key > bestKey) { bestKey = key; best = bit; }
			}
			if (best) moves = best;                       // 危険ラインが無いときだけ自由
			else if (g_defStrategy == 2) moves = hand & -hand;   // 完全固定戦略
			else if (g_defStrategy == 3)
			{
				// 補題 Z6: 静かな段階では「充填手」を避ける。
				// 充填手 = 生きている全空きライン上の埋没マスを、新たに即置可能にしてしまう手
				ull bad = 0;
				for (ull L : g_open)
				{
					if (def & L) continue;
					const ull buried = L & ~occ & ~hand;      // L の埋没している空きマス
					bad |= (buried >> 16) & hand;             // その直下(即置可能なもの)
				}
				const ull cand = hand & ~bad;
				moves = cand ? (cand & -cand) : (hand & -hand);
			}
		}
		res = true;
		for (ull x = moves; x && res; x &= x - 1)
		{
			const ull bit = x & -x;
			res = g_atkIsBlack ? aux(B, W | bit) : aux(B | bit, W);
		}
	}
	g_memo[{B, W}] = res ? 1 : 0;
	return res;
}

// ---------------------------------------------------------------- 厳密解と R2
static const ull MASKL[5] = {0, M1, M2, M3, 0xffff000000000000uLL};
struct TTE { ull me, you; int val; };
static vector<TTE> g_tt(1 << 24);
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

static int ruleR2(int turn, ull rMe, ull rYou)
{
	const bool blackToMove = (turn & 1) != 0;
	const ull rB = blackToMove ? rMe : rYou, rW = blackToMove ? rYou : rMe;
	for (int m = 1; m <= 4; m++)
	{
		if ((m & 1) && (rB & MASKL[m])) return blackToMove ? +1 : -1;
		if (!(m & 1) && (rW & MASKL[m])) return blackToMove ? -1 : +1;
	}
	return 0;
}

// R3 の意味での「詰まる側」: 自由マス(リーチを含まない柱のマス)の総数の偶奇で決まる
// 0 = 黒, 1 = 白
static int stuck_player(ull B, ull W, int turn)
{
	const ull occ = B | W, emp = ~occ;
	const ull reach = (Board::reach(B) & ~W & emp) | (Board::reach(W) & ~B & emp);
	int Nfree = 0;
	for (int c = 0; c < 16; c++)
	{
		int cells = 0; bool hasReach = false;
		for (int z = 0; z < 4; z++)
		{
			const int i = c + 16 * z;
			if (occ >> i & 1) continue;
			cells++;
			if (reach >> i & 1) hasReach = true;
		}
		if (!hasReach) Nfree += cells;       // ブロックを持たない柱 = ぜんぶ自由マス
	}
	const int mover = (turn & 1) ? 0 : 1;
	return (Nfree % 2 == 0) ? mover : (1 - mover);
}

// ---------------------------------------------------------------- 局面構成(G_A2 の幾何を満たす形状)
static int h[16];
static ull g_empty, g_hand;
static int g_ecount[LINES_NUM];
static int g_cells[64], g_ncell;

// g_shapeMode = 1 : 全空きの H4 ライン(4 本の一直線柱がすべて非満杯)を強制的に作る。
//                   補題B より高さ 2 以上は高々 2 本なので、その範囲で高さを振る。
static int g_shapeMode = 0;
static bool locked[16];

static bool make_shape(int E)
{
	for (int c = 0; c < 16; c++) { h[c] = 0; locked[c] = false; }
	int rest = E;
	if (g_shapeMode == 1)
	{
		const int *s = COLSET[rndi(10)];
		int hh[4] = {1, 1, 1, 1};
		const int extra = rndi(3);                       // 高さ 2 の柱を 0〜2 本
		for (int k = 0; k < extra; k++) hh[rndi(4)] = 2;
		int k2 = 0; for (int k = 0; k < 4; k++) if (hh[k] >= 2) k2++;
		if (k2 > 2) return false;                        // 補題B
		int used = 0;
		for (int k = 0; k < 4; k++) { h[s[k]] = hh[k]; locked[s[k]] = true; used += hh[k]; }
		if (used > E) return false;
		rest = E - used;
	}
	else if (g_shapeMode == 3)
	{
		// 全空き H4 ラインを 3 本強制する(3 本以上の交差)
		int pick[3];
		pick[0] = rndi(10); pick[1] = rndi(10); pick[2] = rndi(10);
		if (pick[0] == pick[1] || pick[1] == pick[2] || pick[0] == pick[2]) return false;
		int cols[16], nc = 0;
		for (int k = 0; k < 3; k++)
			for (int i = 0; i < 4; i++)
			{
				bool dup = false;
				for (int j = 0; j < nc; j++) if (cols[j] == COLSET[pick[k]][i]) dup = true;
				if (!dup) cols[nc++] = COLSET[pick[k]][i];
			}
		if (nc > E) return false;
		for (int i = 0; i < nc; i++) { h[cols[i]] = 1; locked[cols[i]] = true; }
		rest = E - nc;
		int guard3 = 0;
		while (rest > 0)
		{
			if (++guard3 > 2000) break;                  // 残りは他の柱へ
			const int c = cols[rndi(nc)];
			if (h[c] >= 2) continue;
			h[c] = 2;
			int bad = 0;
			for (int k = 0; k < 3; k++)
			{
				int k2 = 0;
				for (int i = 0; i < 4; i++) if (h[COLSET[pick[k]][i]] >= 2) k2++;
				if (k2 > 2) bad = 1;                     // 補題B
			}
			if (bad) { h[c] = 1; continue; }
			rest--;
		}
	}
	else if (g_shapeMode == 2)
	{
		// 柱を 1 本だけ共有する 2 本の全空き H4 ラインを強制する(交差ケース)
		const int a = rndi(10), b = rndi(10);
		if (a == b) return false;
		int shared = 0;
		for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (COLSET[a][i] == COLSET[b][j]) shared++;
		if (shared != 1) return false;
		int cols[8], nc = 0;
		for (int i = 0; i < 4; i++) cols[nc++] = COLSET[a][i];
		for (int j = 0; j < 4; j++)
		{
			bool dup = false;
			for (int i = 0; i < 4; i++) if (COLSET[a][i] == COLSET[b][j]) dup = true;
			if (!dup) cols[nc++] = COLSET[b][j];
		}
		if (nc != 7 || E < 7) return false;
		for (int i = 0; i < nc; i++) { h[cols[i]] = 1; locked[cols[i]] = true; }
		rest = E - 7;
		// 余りは 7 本のうちどれかを高さ 2 にして消費(各ラインで h>=2 が 2 本を超えないこと = 補題B)
		int guard2 = 0;
		while (rest > 0)
		{
			if (++guard2 > 2000) break;   // 残りは他の柱へ
			const int c = cols[rndi(nc)];
			if (h[c] >= 2) continue;
			h[c] = 2;
			int bad = 0;
			for (int k = 0; k < 2; k++)
			{
				const int *s2 = COLSET[k == 0 ? a : b];
				int k2 = 0; for (int i = 0; i < 4; i++) if (h[s2[i]] >= 2) k2++;
				if (k2 > 2) bad = 1;
			}
			if (bad) { h[c] = 1; continue; }
			rest--;
		}
	}
	if (rndi(3) != 0) { const int ht = 3 + rndi(2); const int c = rndi(16);
	                    if (!locked[c] && ht <= rest) { h[c] = ht; locked[c] = true; rest -= ht; } }
	int guard = 0;
	while (rest > 0)
	{
		if (++guard > 10000) return false;
		const int c = rndi(16);
		if (locked[c] || h[c] >= 2) continue;
		h[c]++; rest--;
	}
	g_empty = 0;
	for (int c = 0; c < 16; c++)
		for (int k = 0; k < h[c]; k++) g_empty |= 1uLL << (c + 16 * (3 - k));
	g_hand = handmask(~g_empty);
	g_ncell = 0;
	for (int i = 0; i < 64; i++) if (!(g_empty >> i & 1)) g_cells[g_ncell++] = i;
	for (int i = 0; i < LINES_NUM; i++)
	{
		g_ecount[i] = __builtin_popcountll(LINES[i] & g_empty);
		if (g_ecount[i] == 3) return false;                   // G_A2 の幾何条件
	}
	return true;
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
		else if (ec == 1)
		{
			const ull em = LINES[i] & g_empty;
			if (!(em & g_hand))
			{
				// 埋没リーチ。g_forceDraw なら「有効脅威」を禁止して m* = ∞ に追い込む
				if (g_forceDraw)
				{
					const int lev = (int)(__builtin_ctzll(em) / 16) + 1;
					const int own = (lev & 1) ? 0 : 1;             // 0 = 黒, 1 = 白
					if ((cb == 3 && own == 0) || (cw == 3 && own == 1)) e++;
				}
				continue;
			}
			if (cb == 3 || cw == 3) e++;                           // 制約(C) 違反
		}
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

int main(int argc, char **argv)
{
	init_lines();
	const int turn = argc > 1 ? atoi(argv[1]) : 57;
	const long long trials = argc > 2 ? atoll(argv[2]) : 50000;
	if (argc > 3) rs = (ull)atoll(argv[3]) * 0x9e3779b97f4a7c15uLL + 12345;
	if (argc > 4) g_strictSuccess = atoi(argv[4]);
	if (argc > 5) g_realistic = atoi(argv[5]);
	if (argc > 6) g_shapeMode = atoi(argv[6]);
	if (argc > 7) g_forceDraw = atoi(argv[7]);
	if (argc > 8) g_defStrategy = atoi(argv[8]);
	const int E = 65 - turn;

	long long pass = 0, okBlack = 0, okWhite = 0, nOpen = 0, nMulti = 0;
	long long nPredDraw = 0, nR2bad = 0, nCreate = 0, nCreateR2bad = 0, nCreatorStuck = 0, nDrawPred = 0, nDrawPredAtkWin = 0;
	int shown = 0;

	for (long long it = 0; it < trials; it++)
	{
		if (!make_shape(E)) continue;
		ull B, W;
		if (!color_it(turn, B, W)) continue;
		const ull occ = B | W;
		if (__builtin_popcountll(occ) + 1 != turn) continue;
		if (Board::win(B) == State::End || Board::win(W) == State::End) continue;
		const ull hand = handmask(occ);
		if ((hand & Board::reach(B) & ~W) || (hand & Board::reach(W) & ~B)) continue;   // 制約(C)
		if (!gate_A2(B, W) || !gate_T(occ) || !gate_H3(occ)) continue;
		pass++;

		g_open.clear();
		for (int i = 0; i < LINES_NUM; i++) if (!(occ & LINES[i])) g_open.push_back(LINES[i]);
		nOpen += g_open.size();
		if (g_open.size() >= 2) nMulti++;
		if (g_open.empty()) { okBlack++; okWhite++; continue; }

		Board bd; bd.Me = (turn & 1) ? B : W; bd.You = (turn & 1) ? W : B;
		const ull rMe = Board::reach(bd.Me) & ~bd.You, rYou = Board::reach(bd.You) & ~bd.Me;
		const int exact = solve(bd), pred = ruleR2(turn, rMe, rYou);
		if (pred != exact) nR2bad++;
		const int stuck = stuck_player(B, W, turn);
		if (pred == 0) nPredDraw++;
		if (pred == 0) nPredDraw++;

		for (int atkBlack = 0; atkBlack < 2; atkBlack++)
		{
			g_atkIsBlack = atkBlack;
			g_memo.clear();
			const bool created = aux(B, W);
			if (!created) { (atkBlack ? okBlack : okWhite)++; continue; }

			// 創出できた局面についての内訳
			nCreate++;
			if (pred != exact) nCreateR2bad++;
			if (stuck == atkBlack) nCreatorStuck++;             // 創出側が「詰まる側」だったか
			// R2 が引き分けと言っているのに創出側が勝てるか
			const bool atkWins = atkBlack ? ((turn & 1) ? exact > 0 : exact < 0)
			                              : ((turn & 1) ? exact < 0 : exact > 0);
			if (pred == 0) { nDrawPred++; if (atkWins) nDrawPredAtkWin++; }
			if (shown < 2)
			{
				shown++;
				printf("\n===== 創出可能な局面の例(攻撃側 = %s)=====\n", atkBlack ? "黒" : "白");
				bd.print();
				printf("  turn=%d 全空きライン %zu 本  R2=%+d 厳密=%+d  詰まる側=%s\n",
				       turn, g_open.size(), pred, exact, stuck ? "白" : "黒");
				fflush(stdout);
			}
		}
	}

	printf("\n[定理 C1 の機械検証]  turn=%d (E=%d)  試行 %lld\n", turn, E, trials);
	printf("  G_A2 ∧ G_T ∧ G_3 通過局面        : %lld\n", pass);
	printf("  うち全空きラインが 2 本以上       : %lld\n", nMulti);
	printf("  全空きラインの総数               : %lld\n", nOpen);
	printf("  黒が創出できなかった局面          : %lld / %lld\n", okBlack, pass);
	printf("  白が創出できなかった局面          : %lld / %lld\n", okWhite, pass);
	printf("\n[補題 Z の検証]\n");
	printf("  R2 が厳密解と食い違った局面          : %lld / %lld\n", nR2bad, pass);
	printf("  創出が成立した (局面, 攻撃色) 組      : %lld\n", nCreate);
	printf("   うち R2 が食い違ったもの            : %lld\n", nCreateR2bad);
	printf("   うち創出側が「詰まる側」だったもの   : %lld (%.1f%%)\n", nCreatorStuck,
	       nCreate ? 100.0 * nCreatorStuck / nCreate : 0.0);
	printf("  R2 が引き分けと判定した局面(分母)  : %lld / %lld\n", nPredDraw, pass);
	printf("   そのうち創出が成立した組            : %lld  ← 0 なら補題 Z' が成立\n", nDrawPred);
	printf("    そのうち創出側が実際に勝てた        : %lld  ← 0 なら補題 Z の結論が成立\n", nDrawPredAtkWin);
	printf("  → 定理 C1 の結論は %s\n",
	       (okBlack == pass && okWhite == pass) ? "この標本では成立" : "反例あり");
	return 0;
}
