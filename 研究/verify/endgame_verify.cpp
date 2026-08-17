// 最終盤(残り空きマス数が少ない局面)の厳密解と、簡略化評価関数候補の一致検証。
//
// 目的:
//   1. 現行 evaluate_alpha_t.hpp の turn>=60 分岐(= 規則 R0)が厳密かどうかを確認する
//   2. 段パリティ定理から導いた規則(R1/R2)の正しさを確認する
//
// 局面の生成は探索木の葉と同じ条件を再現する:
//   - どの祖先ノードでも手番側に即勝ち手が無い(あればそのノードで探索は打ち切られる)
//   - 相手に即リーチがあれば必ず阻止手に限定される
//   - 葉自身は「双方とも即座に置けるリーチが無い」= 研究計画の制約(C)
//
// ビルド: g++ -O2 -std=c++17 -o endgame_verify.exe endgame_verify.cpp
#include "../../code/common.hpp"
#include "../../code/board.hpp"

typedef unsigned long long ull;

static const ull M1 = 0x000000000000ffffuLL;   // 段1 (z=0)
static const ull M2 = 0x00000000ffff0000uLL;   // 段2 (z=1)
static const ull M3 = 0x0000ffff00000000uLL;   // 段3 (z=2)
static const ull M4 = 0xffff000000000000uLL;   // 段4 (z=3)
static const ull MASK[5] = {0, M1, M2, M3, M4};

// ---------------------------------------------------------------- 厳密解
// 手番側視点で +1(勝ち) / 0(引き分け) / -1(負け)
static int solve(const Board &b)
{
	ull hand = b.valid_move();
	if (!hand) return 0;
	const ull rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou)
	{
		if (__builtin_popcountll(hand & rYou) > 1) return -1;   // 二重脅威は防げない
		hand &= rYou;                                          // 阻止一手に強制
	}
	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand;
		hand ^= bit;
		const int v = -solve(b.place_fast_clone(bit));
		if (v > best) best = v;
		if (best == 1) break;
	}
	return best;
}

// ---------------------------------------------------------------- 規則たち
struct Feat
{
	ull rMe, rYou;      // 手番側 / 相手側のリーチ(空きマス上のみ)
	ull rB, rW;         // 黒 / 白のリーチ
	Color now;          // 手番の色
	int turn;
};

// R0: 現行実装 (evaluate_alpha_t.hpp reach_layer_intersection_t の turn>=60 分岐)
static int ruleR0(const Feat &f)
{
	ull rMe = f.rMe, rYou = f.rYou;
	const ull rMe_tmp = rMe;
	rMe = rMe & ~(rYou << 16);
	rYou = rYou & ~(rMe_tmp << 16);
	const ull inter3 = (rMe & rYou) & M3;
	rMe ^= inter3;
	rYou ^= inter3;
	if (f.now == Color::Black)
	{
		if ((rMe & M3) || inter3) return +1;
		if ((rYou & M2) || (rYou & M4)) return -1;
	}
	else
	{
		if (rMe & M4) return +1;
		if ((rYou & M3) || inter3) return -1;
	}
	return 0;
}

// R0a: R0 の欠陥(A)「白番分岐に白の段2 脅威の判定が無い」だけを修正した版
static int ruleR0a(const Feat &f)
{
	ull rMe = f.rMe, rYou = f.rYou;
	const ull rMe_tmp = rMe;
	rMe = rMe & ~(rYou << 16);
	rYou = rYou & ~(rMe_tmp << 16);
	const ull inter3 = (rMe & rYou) & M3;
	rMe ^= inter3;
	rYou ^= inter3;
	if (f.now == Color::Black)
	{
		if ((rMe & M3) || inter3) return +1;
		if (rYou & (M2 | M4)) return -1;
	}
	else
	{
		if (rMe & (M2 | M4)) return +1;
		if ((rYou & M3) || inter3) return -1;
	}
	return 0;
}

// R1: 段パリティ規則(黒=奇数段 / 白=偶数段)。競合時は黒優先(R0 と同じ優先順)
static int ruleR1(const Feat &f)
{
	const bool bwin = (f.rB & (M1 | M3)) != 0;
	const bool wwin = (f.rW & (M2 | M4)) != 0;
	int v = 0;
	if (bwin) v = +1;
	else if (wwin) v = -1;
	return f.now == Color::Black ? v : -v;
}

// R2: 段パリティ規則 + 競合時は「段が最も低い有効脅威」が勝つ
static int ruleR2(const Feat &f)
{
	for (int m = 1; m <= 4; m++)
	{
		const bool b = (m & 1) && (f.rB & MASK[m]);
		const bool w = !(m & 1) && (f.rW & MASK[m]);
		if (b) return f.now == Color::Black ? +1 : -1;
		if (w) return f.now == Color::White ? +1 : -1;
	}
	return 0;
}

// R2impl: 研究結果ドキュメント §7 で提案している「現行コードへの置き換え案」そのもの。
// ruleR2 と完全に同じ値を返すことを検証するために置いている。
static int ruleR2impl(const Feat &f)
{
	ull rMe = f.rMe, rYou = f.rYou;
	const ull rMe_tmp = rMe;
	rMe = rMe & ~(rYou << 16);            // エスケープフィルタ(現行のまま)
	rYou = rYou & ~(rMe_tmp << 16);
	const ull inter3 = (rMe & rYou) & M3;
	rMe ^= inter3;
	rYou ^= inter3;

	const ull rB = (f.now == Color::Black) ? rMe : rYou;
	const ull rW = (f.now == Color::Black) ? rYou : rMe;
	int v = 0;
	if      (rW & M2)                v = -1;   // 白の段2
	else if ((rB & M3) || inter3)    v = +1;   // 黒の段3
	else if (rW & M4)                v = -1;   // 白の段4
	return f.now == Color::Black ? v : -v;
}

// R2 を葉に使った d 手読み(探索本体と同じ強制手処理)
static int search_with_R2(const Board &b, int depth)
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
	else if (depth <= 0)
	{
		Feat f;
		f.turn = b.turn();
		f.now = ((f.turn - 1) & 1) ? Color::White : Color::Black;
		f.rMe = rMe; f.rYou = rYou;
		if (f.now == Color::Black) { f.rB = rMe; f.rW = rYou; }
		else { f.rB = rYou; f.rW = rMe; }
		return ruleR2(f);
	}
	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand;
		hand ^= bit;
		const int v = -search_with_R2(b.place_fast_clone(bit), depth - 1);
		if (v > best) best = v;
		if (best == 1) break;
	}
	return best;
}

// 「脅威創出不可能」判定: どちらかの色が 2 個だけ入った未確定ラインが 1 本でもあれば
// 一手で新しいリーチを作れる(= BoardInc の cnt[] における v==±2、既存 flag_tbl と同一条件)。
static bool creation_free(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if (cm == 2 && cy == 0) return false;
		if (cy == 2 && cm == 0) return false;
	}
	return true;
}

// ---------------------------------------------------------------- 集計
struct Stat
{
	long long n = 0;
	long long ok = 0;
	long long miss = 0;      // 引き分けと判定したが実際は決着(不完全)
	long long wrong = 0;     // 勝敗を逆または過大に判定(不健全)
	Board example_miss, example_wrong;
	bool has_miss = false, has_wrong = false;
};

static void tally(Stat &s, int pred, int exact, const Board &b)
{
	s.n++;
	if (pred == exact) { s.ok++; return; }
	if (pred == 0) { s.miss++; if (!s.has_miss) { s.example_miss = b; s.has_miss = true; } }
	else { s.wrong++; if (!s.has_wrong) { s.example_wrong = b; s.has_wrong = true; } }
}

static const int TMIN = 56, TMAX = 64;

struct TurnData
{
	Stat r0, r0a, r1, r2, s[4];   // s[d] = R2 を葉に使った d 手読み
	Stat cf0, cf2;           // 脅威創出不可能な局面に限定した R0 / R2
	long long win = 0, draw = 0, lose = 0;                 // 手番側視点の厳密解分布
	map<vector<int>, long long> shape;                     // 空きマスの柱形状
	long long conflict = 0, conflict_lowwin = 0;           // R1 の競合ケース
};
static TurnData TD[TMAX + 1];

static vector<int> shape_of(const Board &b)
{
	const ull occ = b.Me | b.You;
	vector<int> h;
	for (int c = 0; c < 16; c++)
	{
		int e = 0;
		for (int z = 0; z < 4; z++) if (!(occ >> (c + 16 * z) & 1)) e++;
		if (e) h.push_back(e);
	}
	sort(h.rbegin(), h.rend());
	return h;
}

// 局面の空きマスとリーチ構造を人間が読める形で出力する
static void dump(const Board &b)
{
	const int turn = b.turn();
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const ull rB = (now == Color::Black) ? rMe : rYou;
	const ull rW = (now == Color::Black) ? rYou : rMe;
	const ull occ = b.Me | b.You, hand = b.valid_move();
	printf("  turn=%d(手番=%s) 厳密解(手番視点)=%+d  R0=%+d R2=%+d\n",
	       turn, now == Color::Black ? "黒" : "白", solve(b),
	       [&]{ Feat f; f.turn=turn; f.now=now; f.rMe=rMe; f.rYou=rYou; f.rB=rB; f.rW=rW; return ruleR0(f); }(),
	       [&]{ Feat f; f.turn=turn; f.now=now; f.rMe=rMe; f.rYou=rYou; f.rB=rB; f.rW=rW; return ruleR2(f); }());
	b.print();
	printf("  空きマス:");
	for (int i = 0; i < 64; i++) if (!(occ >> i & 1))
	{
		printf("  (x%d,y%d,段%d)%s%s%s", X(i) + 1, Y(i) + 1, Z(i) + 1,
		       (hand >> i & 1) ? "[即置可]" : "",
		       (rB >> i & 1) ? "[黒リーチ]" : "", (rW >> i & 1) ? "[白リーチ]" : "");
	}
	printf("\n");

	// 最善手順(PV)を表示
	printf("  最善手順:");
	Board cur = b;
	for (int ply = 0; ply < 16; ply++)
	{
		ull hand = cur.valid_move();
		if (!hand) { printf("  →空きマス無し(引き分け)"); break; }
		const int me_turn = cur.turn();
		const char *who = ((me_turn - 1) & 1) ? "白" : "黒";
		const ull rM = Board::reach(cur.Me) & ~cur.You;
		if (hand & rM)
		{
			const int i = __builtin_ctzll(hand & rM);
			printf("  %s(x%d,y%d,段%d)*勝ち", who, X(i) + 1, Y(i) + 1, Z(i) + 1);
			break;
		}
		const ull rY = Board::reach(cur.You) & ~cur.Me;
		if (hand & rY) hand &= rY;
		int best = -2; ull bestbit = 0;
		ull h = hand;
		while (h)
		{
			const ull bit = h & -h; h ^= bit;
			const int v = -solve(cur.place_fast_clone(bit));
			if (v > best) { best = v; bestbit = bit; }
		}
		const int i = __builtin_ctzll(bestbit);
		printf("  %s(x%d,y%d,段%d)", who, X(i) + 1, Y(i) + 1, Z(i) + 1);
		cur = cur.place_fast_clone(bestbit);
	}
	printf("\n");
}

static void examine(const Board &b, int turn)
{
	Feat f;
	f.turn = turn;
	f.now = ((turn - 1) & 1) ? Color::White : Color::Black;
	f.rMe = Board::reach(b.Me) & ~b.You;
	f.rYou = Board::reach(b.You) & ~b.Me;
	if (f.now == Color::Black) { f.rB = f.rMe; f.rW = f.rYou; }
	else { f.rB = f.rYou; f.rW = f.rMe; }

	const int exact = solve(b);
	TurnData &t = TD[turn];
	if (exact > 0) t.win++; else if (exact < 0) t.lose++; else t.draw++;
	t.shape[shape_of(b)]++;
	tally(t.r0, ruleR0(f), exact, b);
	tally(t.r0a, ruleR0a(f), exact, b);
	if (ruleR2impl(f) != ruleR2(f)) { printf("!! R2impl != R2 at turn %d\n", turn); dump(b); exit(1); }
	tally(t.r1, ruleR1(f), exact, b);
	tally(t.r2, ruleR2(f), exact, b);
	for (int d = 1; d <= 3; d++) tally(t.s[d], search_with_R2(b, d), exact, b);
	if (creation_free(b)) { tally(t.cf0, ruleR0(f), exact, b); tally(t.cf2, ruleR2(f), exact, b); }

	if ((f.rB & (M1 | M3)) && (f.rW & (M2 | M4)))
	{
		t.conflict++;
		if (ruleR2(f) == exact) t.conflict_lowwin++;
	}
}

int main(int argc, char **argv)
{
	init_lines();
	const long long trials = argc > 1 ? atoll(argv[1]) : 2000000;

	for (long long it = 0; it < trials; it++)
	{
		Board b;
		for (int turn = 1; turn <= TMAX; turn++)
		{
			ull hand = b.valid_move();
			if (!hand) break;
			const ull rMe = Board::reach(b.Me) & ~b.You;
			if (hand & rMe) break;                    // 即勝ち手あり → 探索はここで打ち切る
			const ull rYou = Board::reach(b.You) & ~b.Me;
			if (!(hand & rYou) && turn >= TMIN) examine(b, turn);   // 制約(C)成立 = 葉候補
			if (hand & rYou) hand &= rYou;            // 阻止手に強制
			int k = (int)(rng() % __builtin_popcountll(hand));
			ull h = hand;
			while (k--) h &= h - 1;
			b = b.place_fast_clone(h & -h);
		}
	}

	printf("playouts = %lld\n\n", trials);
	printf("%4s %10s %8s %8s %8s | %-26s | %-26s | %-26s\n",
	       "turn", "samples", "win", "draw", "lose", "R0 (現行実装)", "R1 (段パリティ/黒優先)", "R2 (段パリティ/低段優先)");
	for (int t = TMAX; t >= TMIN; t--)
	{
		const TurnData &d = TD[t];
		if (!d.r0.n) continue;
		printf("%4d %10lld %8lld %8lld %8lld | ok%8lld miss%6lld bad%4lld | ok%8lld miss%6lld bad%4lld | ok%8lld miss%6lld bad%4lld\n",
		       t, d.r0.n, d.win, d.draw, d.lose,
		       d.r0.ok, d.r0.miss, d.r0.wrong,
		       d.r1.ok, d.r1.miss, d.r1.wrong,
		       d.r2.ok, d.r2.miss, d.r2.wrong);
	}

	printf("\n[現行実装の欠陥切り分け]\n");
	printf("%4s %10s | %-24s | %-24s | %-24s\n", "turn", "samples", "R0 (現行)", "R0a (欠陥A のみ修正)", "R2 (欠陥A+B 修正)");
	for (int t = TMAX; t >= TMIN; t--)
	{
		const TurnData &d = TD[t];
		if (!d.r0.n) continue;
		printf("%4d %10lld | ok%8lld miss%6lld bad%5lld | ok%8lld miss%6lld bad%5lld | ok%8lld miss%6lld bad%5lld\n",
		       t, d.r0.n, d.r0.ok, d.r0.miss, d.r0.wrong,
		       d.r0a.ok, d.r0a.miss, d.r0a.wrong, d.r2.ok, d.r2.miss, d.r2.wrong);
	}

	printf("\n[R2 を葉に使った d 手読みの精度]\n");
	printf("%4s %10s | %-22s | %-22s | %-22s\n", "turn", "samples", "d=1", "d=2", "d=3");
	for (int t = TMAX; t >= TMIN; t--)
	{
		const TurnData &d = TD[t];
		if (!d.r0.n) continue;
		printf("%4d %10lld", t, d.r0.n);
		for (int k = 1; k <= 3; k++)
			printf(" | ok%8lld miss%6lld bad%4lld", d.s[k].ok, d.s[k].miss, d.s[k].wrong);
		printf("\n");
	}

	printf("\n[脅威創出が不可能な局面に限定した精度]\n");
	printf("%4s %10s %7s | %-26s | %-26s\n", "turn", "該当数", "割合", "R0 (現行実装)", "R2 (段パリティ/低段優先)");
	for (int t = TMAX; t >= TMIN; t--)
	{
		const TurnData &d = TD[t];
		if (!d.r0.n) continue;
		printf("%4d %10lld %6.1f%% | ok%8lld miss%6lld bad%4lld | ok%8lld miss%6lld bad%4lld\n",
		       t, d.cf2.n, 100.0 * d.cf2.n / d.r0.n,
		       d.cf0.ok, d.cf0.miss, d.cf0.wrong, d.cf2.ok, d.cf2.miss, d.cf2.wrong);
	}

	printf("\n[R1 競合(黒に奇数段脅威かつ白に偶数段脅威)ケース]\n");
	for (int t = TMAX; t >= TMIN; t--)
		if (TD[t].conflict) printf("  turn %d : %lld 件 (R2=低段優先で的中 %lld 件)\n", t, TD[t].conflict, TD[t].conflict_lowwin);

	printf("\n[空きマス形状の分布]\n");
	for (int t = TMAX; t >= TMIN; t--)
	{
		if (!TD[t].r0.n) continue;
		printf("  turn %d (E=%d):", t, 65 - t);
		for (const auto &kv : TD[t].shape)
		{
			printf("  ");
			for (size_t i = 0; i < kv.first.size(); i++) printf("%s%d", i ? "+" : "", kv.first[i]);
			printf(":%lld", kv.second);
		}
		printf("\n");
	}

	// 反例の実例を表示
	for (int t = 62; t >= 60; t--)
	{
		const TurnData &d = TD[t];
		if (d.r0.has_wrong) { printf("\n[R0 不健全 例 turn=%d]\n", t); dump(d.r0.example_wrong); }
		if (d.r2.has_wrong) { printf("\n[R2 不健全 例 turn=%d]\n", t); dump(d.r2.example_wrong); }
		if (d.r2.has_miss)  { printf("\n[R2 不完全 例 turn=%d]\n", t); dump(d.r2.example_miss); }
	}
	return 0;
}
