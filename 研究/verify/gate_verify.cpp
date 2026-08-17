// 「2石+空き2ライン(脅威創出可能性)」を適用条件(ゲート)に使った場合の、
// 段パリティ規則 R2 の適用開始手数と精度を実盤面で測定する。
//
// ゲート:
//   G_A  創出不可能    : どの色も「2石 + 空き2」のラインを持たない(= BoardInc の cnt が 0x20/0x02 でない)
//   G_T  高い柱が1本以下: 空きマス3個以上の柱が高々1本(抽象モデルの完全列挙で導いた構造条件)
//   G_AT G_A かつ G_T
//   G_C  テンポ限定    : 「2石+空き2」のうち、今すぐ即置可能マスにリーチを作れるものが無い(G_A より緩い)
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o gate_verify.exe gate_verify.cpp
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;

static const ull M1 = 0x000000000000ffffuLL;
static const ull M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL;
static const ull M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

// ---------------------------------------------------------------- 置換表つき厳密解
struct TTE { ull me, you; int val; };
static const int TTBITS = 22;
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

// ---------------------------------------------------------------- 規則 R2
static int ruleR2(const Board &b, int turn, ull rMe, ull rYou)
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

// G_A より厳しい版: 「1石+空き3」ラインも排除する
// (2手かけて 3 石にすればリーチを作れるため。turn=60 の取りこぼしの原因)
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

// 今すぐ「即置可能マスに新リーチを作る手」が存在しないか
static bool gate_C(const Board &b)
{
	const ull hand = b.valid_move();
	const ull empty = ~(b.Me | b.You);
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if (!((cm == 2 && cy == 0) || (cy == 2 && cm == 0))) continue;
		ull e2 = LINES[i] & empty;                       // 空き 2 マス
		const ull p = e2 & -e2, q = e2 ^ p;
		// p に置いて q にリーチができ、その q が即置可能(または p の真上)ならテンポ手になる
		if ((hand & p) && ((hand & q) || q == (p << SIZE * SIZE))) return false;
		if ((hand & q) && ((hand & p) || p == (q << SIZE * SIZE))) return false;
	}
	return true;
}

// ---------------------------------------------------------------- 集計
enum { G_NONE, G_A, G_T, G_AT, G_C, G_A2, G_A2T, NGATE };
static const char *GNAME[NGATE] = {"ゲート無し", "G_A 創出不可", "G_T 高柱<=1", "G_AT A かつ T", "G_C テンポ限定", "G_A2 1石ラインも排除", "G_A2T A2 かつ T"};

struct Stat { long long n = 0, ok = 0, miss = 0, bad = 0, decided = 0, decided_ok = 0; };

static const int TMIN = 46, TMAX = 64, SOLVE_ALL_FROM = 56;

struct TurnData
{
	long long samples = 0;
	long long pass[NGATE] = {0};
	Stat st[NGATE];
	Board ex_miss[NGATE]; bool has_miss[NGATE] = {false};
	Board ex_bad[NGATE];  bool has_bad[NGATE] = {false};
};
static TurnData TD[TMAX + 1];

static void examine(const Board &b, int turn)
{
	TurnData &t = TD[turn];
	t.samples++;

	bool pass[NGATE];
	const bool a = gate_A(b), tt = gate_T(b), c = gate_C(b), a2 = gate_A2(b);
	pass[G_NONE] = true; pass[G_A] = a; pass[G_T] = tt; pass[G_AT] = a && tt; pass[G_C] = c; pass[G_A2] = a2; pass[G_A2T] = a2 && tt;
	for (int g = 0; g < NGATE; g++) if (pass[g]) t.pass[g]++;

	// 深い手数では全件解くのが高コストなので、ゲート通過局面だけ厳密解を求める
	// 深い手数(空きマスが多い)で全件解くのは非現実的なので、
	// turn < SOLVE_ALL_FROM では最も厳しいゲート G_A を通った局面だけ厳密解を求める。
	const bool need = (turn >= SOLVE_ALL_FROM) || (turn >= 52 && (pass[G_A] || pass[G_A2]));
	if (!need) return;

	const int exact = solve(b);
	const ull rMe = Board::reach(b.Me) & ~b.You;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	const int pred = ruleR2(b, turn, rMe, rYou);

	for (int g = 0; g < NGATE; g++)
	{
		if (!pass[g]) continue;
		if (g == G_NONE && turn < SOLVE_ALL_FROM) continue;   // 無ゲートは全件解いた手数だけ集計
		Stat &s = t.st[g];
		s.n++;
		if (pred != 0) { s.decided++; if (pred == exact) s.decided_ok++; }
		if (pred == exact) s.ok++;
		else if (pred == 0) { s.miss++; if (!t.has_miss[g]) { t.ex_miss[g] = b; t.has_miss[g] = true; } }
		else { s.bad++; if (!t.has_bad[g]) { t.ex_bad[g] = b; t.has_bad[g] = true; } }
	}
}

static void dump(const Board &b)
{
	const int turn = b.turn();
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const ull rB = (now == Color::Black) ? rMe : rYou, rW = (now == Color::Black) ? rYou : rMe;
	const ull occ = b.Me | b.You, hand = b.valid_move();
	printf("  turn=%d(手番=%s) 厳密解=%+d R2=%+d  G_A=%d G_T=%d G_C=%d\n", turn,
	       now == Color::Black ? "黒" : "白", solve(b), ruleR2(b, turn, rMe, rYou),
	       gate_A(b), gate_T(b), gate_C(b));
	b.print();
	printf("  空きマス:");
	for (int i = 0; i < 64; i++) if (!(occ >> i & 1))
		printf("  (x%d,y%d,段%d)%s%s%s", X(i) + 1, Y(i) + 1, Z(i) + 1,
		       (hand >> i & 1) ? "[即置可]" : "", (rB >> i & 1) ? "[黒リーチ]" : "", (rW >> i & 1) ? "[白リーチ]" : "");
	printf("\n  最善手順:");
	Board cur = b;
	for (int ply = 0; ply < 20; ply++)
	{
		ull h = cur.valid_move();
		if (!h) { printf("  →引き分け"); break; }
		const char *who = ((cur.turn() - 1) & 1) ? "白" : "黒";
		const ull rM = Board::reach(cur.Me) & ~cur.You;
		if (h & rM) { const int i = __builtin_ctzll(h & rM); printf("  %s(x%d,y%d,段%d)*勝ち", who, X(i)+1, Y(i)+1, Z(i)+1); break; }
		const ull rY = Board::reach(cur.You) & ~cur.Me;
		if (h & rY) h &= rY;
		int best = -2; ull bb = 0;
		for (ull x = h; x; x &= x - 1) { const ull bit = x & -x; const int v = -solve(cur.place_fast_clone(bit)); if (v > best) { best = v; bb = bit; } }
		const int i = __builtin_ctzll(bb);
		printf("  %s(x%d,y%d,段%d)", who, X(i)+1, Y(i)+1, Z(i)+1);
		cur = cur.place_fast_clone(bb);
	}
	printf("\n");
}

int main(int argc, char **argv)
{
	init_lines();
	const long long trials = argc > 1 ? atoll(argv[1]) : 1000000;

	for (long long it = 0; it < trials; it++)
	{
		Board b;
		for (int turn = 1; turn <= TMAX; turn++)
		{
			ull hand = b.valid_move();
			if (!hand) break;
			const ull rMe = Board::reach(b.Me) & ~b.You;
			if (hand & rMe) break;
			const ull rYou = Board::reach(b.You) & ~b.Me;
			if (!(hand & rYou) && turn >= TMIN) examine(b, turn);
			if (hand & rYou) hand &= rYou;
			int k = (int)(rng() % __builtin_popcountll(hand));
			ull h = hand;
			while (k--) h &= h - 1;
			b = b.place_fast_clone(h & -h);
		}
	}

	printf("playouts = %lld\n\n", trials);

	printf("[ゲート通過率(全標本に対する割合)]\n");
	printf("%5s %10s", "turn", "標本数");
	for (int g = 1; g < NGATE; g++) printf(" %14s", GNAME[g]);
	printf("\n");
	for (int t = TMAX; t >= TMIN; t--)
	{
		if (!TD[t].samples) continue;
		printf("%5d %10lld", t, TD[t].samples);
		for (int g = 1; g < NGATE; g++) printf(" %13.3f%%", 100.0 * TD[t].pass[g] / TD[t].samples);
		printf("\n");
	}

	for (int g = 0; g < NGATE; g++)
	{
		printf("\n[%s での R2 の精度]\n", GNAME[g]);
		printf("%5s %10s %8s %8s %8s %10s %10s\n", "turn", "対象数", "一致", "取りこぼし", "誤断定", "決定した数", "うち正解");
		for (int t = TMAX; t >= TMIN; t--)
		{
			const Stat &s = TD[t].st[g];
			if (!s.n) continue;
			printf("%5d %10lld %8lld %8lld %8lld %10lld %10lld\n",
			       t, s.n, s.ok, s.miss, s.bad, s.decided, s.decided_ok);
		}
	}

	for (int t = TMAX; t >= TMIN; t--)
	{
		if (TD[t].has_bad[G_A])  { printf("\n[G_A で誤断定した例 turn=%d]\n", t); dump(TD[t].ex_bad[G_A]); }
		if (TD[t].has_miss[G_A] && t >= 58) { printf("\n[G_A で取りこぼした例 turn=%d]\n", t); dump(TD[t].ex_miss[G_A]); }
	}
	return 0;
}
