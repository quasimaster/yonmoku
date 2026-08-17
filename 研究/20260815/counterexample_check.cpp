// 反例の独立検証。
// board.hpp / common.hpp を一切使わず、ライン生成・リーチ判定・求解・到達可能性判定を
// すべてこのファイル内で独立に実装する(共通バグによる誤検証を避けるため)。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o counterexample_check.exe counterexample_check.cpp
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
using namespace std;
typedef unsigned long long u64;

// ---------------------------------------------------------------- 独立なライン生成
static vector<u64> LN;
static inline int IDX(int x, int y, int z) { return x + 4 * y + 16 * z; }   // 0-origin

static void gen_lines()
{
	for (int dx = -1; dx <= 1; dx++)
	for (int dy = -1; dy <= 1; dy++)
	for (int dz = -1; dz <= 1; dz++)
	{
		if (!dx && !dy && !dz) continue;
		for (int x = 0; x < 4; x++)
		for (int y = 0; y < 4; y++)
		for (int z = 0; z < 4; z++)
		{
			const int ex = x + 3 * dx, ey = y + 3 * dy, ez = z + 3 * dz;
			if (ex < 0 || ex > 3 || ey < 0 || ey > 3 || ez < 0 || ez > 3) continue;
			u64 m = 0;
			for (int k = 0; k < 4; k++) m |= 1uLL << IDX(x + k * dx, y + k * dy, z + k * dz);
			bool dup = false;
			for (u64 q : LN) if (q == m) { dup = true; break; }
			if (!dup) LN.push_back(m);
		}
	}
}

static inline bool has4(u64 b) { for (u64 L : LN) if ((b & L) == L) return true; return false; }
static inline int cnt(u64 b, u64 L) { return __builtin_popcountll(b & L); }

// 「そこに打つと 4 個並びが完成する空きマス」の集合(= 色 b のリーチマス)
static u64 winning_cells(u64 b, u64 emp)
{
	u64 r = 0;
	for (u64 L : LN)
	{
		const u64 rest = L & ~b;
		if (__builtin_popcountll(rest) == 1 && (rest & emp)) r |= rest;
	}
	return r;
}

// ---------------------------------------------------------------- 独立な求解器
static long long nodes = 0;
struct Ent { u64 me, you; int val; bool used; };
static vector<Ent> tt(1u << 25);
static inline u64 hsh(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccduLL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53uLL; return x ^ (x >> 33); }

static u64 playable(u64 occ)
{
	u64 h = 0;
	for (int c = 0; c < 16; c++)
		for (int z = 0; z < 4; z++)
		{
			const int i = c + 16 * z;
			if (!(occ >> i & 1)) { h |= 1uLL << i; break; }
		}
	return h;
}

// 手番側 me の視点で +1 勝ち / 0 引き分け / -1 負け
static int solve2(u64 me, u64 you)
{
	nodes++;
	const u64 occ = me | you, emp = ~occ;
	u64 hand = playable(occ);
	if (!hand) return 0;
	const u64 wMe = winning_cells(me, emp);
	if (hand & wMe) return +1;                       // 今すぐ 4 個並びを作れる
	const u64 wYou = winning_cells(you, emp);
	if (hand & wYou)
	{
		// 相手の即勝ちマスが 2 つ以上 → 塞ぎきれない(補題 3 よりリーチは消えない)。1 つなら塞ぐしかない。
		if (__builtin_popcountll(hand & wYou) > 1) return -1;
		hand &= wYou;
	}
	const u64 key = hsh(me * 0x9e3779b97f4a7c15uLL ^ hsh(you));
	Ent &e = tt[key & ((1u << 25) - 1)];
	if (e.used && e.me == me && e.you == you) return e.val;
	int best = -1;
	for (u64 x = hand; x; x &= x - 1)
	{
		const u64 bit = x & -x;
		const int v = -solve2(you, me | bit);
		if (v > best) best = v;
		if (best == 1) break;
	}
	e.me = me; e.you = you; e.val = best; e.used = true;
	return best;
}

// ---------------------------------------------------------------- 到達可能性(構成的)
static u64 rs2 = 12345678901234567uLL;
static inline u64 rnd2() { rs2 ^= rs2 << 13; rs2 ^= rs2 >> 7; rs2 ^= rs2 << 17; return rs2; }

// 交互着手 + 重力で目標局面に到達する手順を実際に 1 本見つけて出力する。
// 途中で 4 個並びができる手順は「そこで終局してしまう」ので不可とする。
static bool find_order(u64 tb, u64 tw, const int h[16], vector<int> &seq)
{
	const int stones = __builtin_popcountll(tb | tw);
	for (long long trial = 0; trial < 3000000; trial++)
	{
		int fill[16] = {0};
		u64 b = 0, w = 0;
		seq.clear();
		bool ok = true;
		for (int k = 0; k < stones; k++)
		{
			const bool wantBlack = ((k & 1) == 0);
			int cand[16], nc = 0;
			for (int c = 0; c < 16; c++)
			{
				if (fill[c] >= 4 - h[c]) continue;
				const int i = c + 16 * fill[c];
				const bool isBlack = (tb >> i & 1) != 0;
				if (isBlack == wantBlack) cand[nc++] = c;
			}
			if (!nc) { ok = false; break; }
			const int c = cand[rnd2() % (unsigned)nc];
			const int i = c + 16 * fill[c];
			if (wantBlack) b |= 1uLL << i; else w |= 1uLL << i;
			if (has4(wantBlack ? b : w)) { ok = false; break; }
			seq.push_back(i);
			fill[c]++;
		}
		if (ok && b == tb && w == tw) return true;
	}
	return false;
}

// ---------------------------------------------------------------- 局面
// 表記: 行 y=4..1、各行に z=1..4 のブロック、各ブロック x=1..4。X=黒 O=白 -=空き
struct Pos { const char *name; const char *cell[4][4]; };
static const Pos POSLIST[] = {
	{ "反例 A(turn 54・E=11・白番・盤上にリーチが 1 個も無い)", {
		{ "XXOO", "XOOX", "O-XX", "X-OX" },   // y=4
		{ "XXXO", "OOXX", "X-OO", "X-OX" },   // y=3
		{ "OOXX", "XXOO", "OX--", "----" },   // y=2
		{ "OOXO", "OXXO", "XOOX", "O-XO" },   // y=1
	}},
	{ "反例 B(turn 45・E=20・黒番・G_T0 も成立)", {
		{ "OOXX", "XXOO", "X-O-", "----" },   // y=4
		{ "OOXO", "XXOO", "OXXX", "----" },   // y=3
		{ "OOXX", "XXOX", "--XO", "----" },   // y=2
		{ "XXOO", "OOXX", "OOXO", "----" },   // y=1
	}},
};

static void check_one(const Pos &P)
{
	printf("\n================ %s ================\n", P.name);
	u64 B = 0, W = 0, E = 0;
	for (int row = 0; row < 4; row++)
	{
		const int y = 3 - row;                       // row 0 が y=4
		for (int z = 0; z < 4; z++)
			for (int x = 0; x < 4; x++)
			{
				const char ch = P.cell[row][z][x];
				const int i = IDX(x, y, z);
				if (ch == 'X') B |= 1uLL << i;
				else if (ch == 'O') W |= 1uLL << i;
				else E |= 1uLL << i;
			}
	}
	const int turn = __builtin_popcountll(B | W) + 1;
	printf("黒石 %d / 白石 %d / 空き %d  → turn = %d\n",
	       __builtin_popcountll(B), __builtin_popcountll(W), __builtin_popcountll(E), turn);

	// --- 重力の整合性(空きマスは各柱の上部に連続)
	bool grav = true;
	int h[16];
	for (int c = 0; c < 16; c++)
	{
		int e = 0; bool started = false;
		for (int z = 0; z < 4; z++)
		{
			const bool emp = (E >> (c + 16 * z)) & 1;
			if (emp) { started = true; e++; }
			else if (started) grav = false;          // 空きの上に石 = 重力違反
		}
		h[c] = e;
	}
	printf("重力の整合性: %s\n", grav ? "OK" : "違反");
	printf("柱の高さ:");
	for (int c = 0; c < 16; c++) if (h[c]) printf(" (x%d,y%d)=%d", (c & 3) + 1, (c >> 2) + 1, h[c]);
	printf("\n既存の 4 個並び: 黒=%s 白=%s\n", has4(B) ? "あり" : "なし", has4(W) ? "あり" : "なし");

	// --- ゲート
	bool gA2 = true;
	for (u64 L : LN)
	{
		const int cb = cnt(B, L), cw = cnt(W, L);
		if ((cw == 0 && (cb == 1 || cb == 2)) || (cb == 0 && (cw == 1 || cw == 2))) { gA2 = false; break; }
	}
	int tall = 0; for (int c = 0; c < 16; c++) if (h[c] >= 3) tall++;
	bool g3 = true;
	{
		static const int CS[10][4] = {{0,1,2,3},{4,5,6,7},{8,9,10,11},{12,13,14,15},
		                              {0,4,8,12},{1,5,9,13},{2,6,10,14},{3,7,11,15},
		                              {0,5,10,15},{3,6,9,12}};
		for (int k = 0; k < 10; k++)
		{
			bool all = true;
			for (int j = 0; j < 4; j++) if (!((E >> (CS[k][j] + 32)) & 1)) { all = false; break; }
			if (all) { g3 = false; break; }
		}
	}
	printf("ゲート: G_A2=%s  G_T(高い柱 %d 本)=%s  G_T0=%s  G_3=%s\n",
	       gA2 ? "OK" : "NG", tall, tall <= 1 ? "OK" : "NG", tall == 0 ? "OK" : "NG", g3 ? "OK" : "NG");

	// --- 制約(C) とリーチ
	const u64 hand = playable(B | W);
	const u64 rB = winning_cells(B, E), rW = winning_cells(W, E);
	printf("制約(C): 即置可能マス上のリーチ = %s\n", ((rB | rW) & hand) ? "あり(違反)" : "なし(OK)");
	printf("リーチ一覧:");
	if (!(rB | rW)) printf(" (盤上にリーチは 1 個も無い)");
	for (int i = 0; i < 64; i++)
	{
		if (!((rB | rW) >> i & 1)) continue;
		printf("  (x%d,y%d,段%d)%s%s%s", (i & 3) + 1, (i >> 2 & 3) + 1, (i >> 4) + 1,
		       (rB >> i & 1) ? "[黒]" : "", (rW >> i & 1) ? "[白]" : "",
		       (hand >> i & 1) ? "[即置可]" : "[埋没]");
	}
	printf("\n");

	// --- m* と R2
	int mstar = 99;
	for (int m = 1; m <= 4; m++)
	{
		const u64 mask = 0xffffuLL << (16 * (m - 1));
		const u64 eff = (m & 1) ? (rB & mask) : (rW & mask);      // owner(m) のリーチ = 有効脅威
		if (eff & ~hand) { mstar = m; break; }                    // 埋没しているもの
	}
	printf("m* = %s  →  規則 R2 の判定 = %s\n", mstar == 99 ? "∞" : to_string(mstar).c_str(),
	       mstar == 99 ? "引き分け" : ((mstar & 1) ? "黒の勝ち" : "白の勝ち"));

	// --- 厳密解(独立実装)
	const bool blackToMove = (turn & 1);
	const u64 me = blackToMove ? B : W, you = blackToMove ? W : B;
	const int v = solve2(me, you);
	printf("厳密解(手番 %s の視点) = %+d  →  %s   (探索ノード %lld)\n", blackToMove ? "黒" : "白", v,
	       v == 0 ? "引き分け" : (v > 0 ? (blackToMove ? "黒の勝ち" : "白の勝ち") : (blackToMove ? "白の勝ち" : "黒の勝ち")),
	       nodes);

	// --- 到達可能性(手順を実際に構成して出力する)
	vector<int> seq;
	const bool rch = find_order(B, W, h, seq);
	printf("交互着手+重力での到達可能性: %s\n", rch ? "到達可能" : "見つからず");
	if (rch)
	{
		printf("  到達手順(1 手目から。この手順自体が到達可能性の証明書):\n   ");
		for (size_t k = 0; k < seq.size(); k++)
		{
			const int i = seq[k];
			printf(" %2d.%s(x%d,y%d,段%d)", (int)k + 1, (k & 1) ? "白" : "黒", (i & 3) + 1, (i >> 2 & 3) + 1, (i >> 4) + 1);
			if ((k + 1) % 6 == 0) printf("\n   ");
		}
		printf("\n");
	}
}

int main()
{
	gen_lines();
	printf("独立に生成したライン数 = %zu (期待値 76)\n", LN.size());
	for (const Pos &P : POSLIST)
	{
		memset(&tt[0], 0, tt.size() * sizeof(Ent));
		nodes = 0;
		check_one(P);
	}
	return 0;
}
