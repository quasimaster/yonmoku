// 本番コード code/endgame_exact.hpp と code/evaluate_alpha_t.hpp(USE_ENDGAME_R2=1)を
// 直接呼び出して、最終盤の厳密評価が「誤判定ゼロ」であることを再確認する検証プログラム。
//
// 設計書 docs/設計書/最終盤/implementation-plan-endgame-exact.md §5.2 の合格条件:
//   1. ゲート通過局面で誤断定 0 かつ取りこぼし 0(turn 64/63/62/61/60/59)。件数も §0.3 の表と一致
//   2. USE_ENDGAME_R2=1 の reach_layer_intersection_t が参照実装 ruleR2 と全標本で一致
//   3. endgame_tall_le1() が素朴な柱ごとの数え上げと全局面で一致
// 加えて本ファイルでは
//   4. ゲートの SSE2 版 / SWAR 版 / 素朴な 76 ライン走査版 が全局面で一致
//   5. 本番 endgame_value() の符号が参照実装 ruleR2 と全標本で一致
//   を確認する。1 件でも不一致があれば即 exit(1) する。
//
// 局面の生成は探索木の葉と同じ条件(制約(C))を再現する。乱数列は既定シードの mt19937 なので
// gate_verify.cpp / endgame_verify.cpp と同一の標本になり、標本数を突合できる。
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o endgame_exact_verify.exe endgame_exact_verify.cpp
#define USE_ENDGAME_R2 1          // ← evaluate_alpha_t.hpp を R2 版で取り込む
#include "../../code/common.hpp"
#include "../../code/board.hpp"
#include "../../code/board_inc.hpp"
#include "../../code/endgame_exact.hpp"
#include "../../code/evaluate_alpha_t.hpp"

typedef unsigned long long ull;

static const ull M1 = 0x000000000000ffffuLL;
static const ull M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL;
static const ull M4 = 0xffff000000000000uLL;
static const ull MASK[5] = {0, M1, M2, M3, M4};

// ---------------------------------------------------------------- 置換表つき厳密解(基準)
struct TTE { ull me = 0, you = 0; int val = 0; };
static const int TTBITS = 22;
static vector<TTE> g_tt(1 << TTBITS);

static inline ull mix64(ull x)
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
	const ull key = mix64(b.Me * 0x9e3779b97f4a7c15uLL ^ mix64(b.You));
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

// ---------------------------------------------------------------- 参照実装(研究側の定義)
// 段パリティ定理をそのまま段の昇順で列挙した形。本番実装(3 段の分岐)の照合基準。
static int ruleR2_ref(const Board &b, int turn)
{
	const ull rMe = Board::reach(b.Me) & ~b.You;
	const ull rYou = Board::reach(b.You) & ~b.Me;
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

// R0(現行実装)。改善量の対比用。
static int ruleR0_ref(const Board &b, int turn)
{
	ull rMe = Board::reach(b.Me) & ~b.You, rYou = Board::reach(b.You) & ~b.Me;
	const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
	const ull rMe_tmp = rMe;
	rMe &= ~(rYou << 16);
	rYou &= ~(rMe_tmp << 16);
	const ull inter3 = (rMe & rYou) & M3;
	rMe ^= inter3; rYou ^= inter3;
	if (now == Color::Black)
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

// ---------------------------------------------------------------- 素朴なゲート実装(照合基準)
static bool gate_A_naive(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if ((cm == 2 && cy == 0) || (cy == 2 && cm == 0)) return false;
	}
	return true;
}

static bool gate_A2_naive(const Board &b)
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

static bool gate_T_naive(const Board &b)
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

// ---------------------------------------------------------------- 集計
struct Stat { long long n = 0, ok = 0, miss = 0, bad = 0, decided = 0; };

static void tally(Stat &s, int pred, int exact)
{
	s.n++;
	if (pred != 0) s.decided++;
	if (pred == exact) s.ok++;
	else if (pred == 0) s.miss++;
	else s.bad++;
}

static const int TMIN = 56, TMAX = 64;
struct TurnData
{
	long long samples = 0;
	Stat gated;        // 本番 endgame_gate() を通過した局面での本番 endgame_value()
	Stat r0, r2;       // ゲート無しでの R0 / R2(設計書 §3.4 の対比表)
	long long pass = 0;
};
static TurnData TD[TMAX + 1];

static long long n_checked = 0;          // 全ゲート/一致チェックを通した局面数
static long long n_r2eval = 0;           // 評価関数経路(USE_ENDGAME_R2)の照合数

static void fail(const char *what, const Board &b, int turn)
{
	printf("\n!! MISMATCH: %s  (turn=%d Me=%llu You=%llu)\n", what, turn,
	       (unsigned long long)b.Me, (unsigned long long)b.You);
	b.print();
	exit(1);
}

static void examine(const Board &b, int turn)
{
	TurnData &t = TD[turn];
	t.samples++;
	n_checked++;

	const BoardInc bi = BoardInc::from(b);

	// --- (4) ゲート実装の等価性: SSE2 / SWAR / 素朴 76 ライン走査
	const bool a_naive = gate_A_naive(b), a2_naive = gate_A2_naive(b);
	if (eg_gate_A_swar(bi.cnt64)  != a_naive)  fail("gate_A  SWAR != naive", b, turn);
	if (eg_gate_A2_swar(bi.cnt64) != a2_naive) fail("gate_A2 SWAR != naive", b, turn);
#if EG_USE_SSE2
	if (eg_gate_A_sse2(bi.cnt)  != a_naive)  fail("gate_A  SSE2 != naive", b, turn);
	if (eg_gate_A2_sse2(bi.cnt) != a2_naive) fail("gate_A2 SSE2 != naive", b, turn);
#endif
	if (endgame_gate_A(bi)  != a_naive)  fail("endgame_gate_A  != naive", b, turn);
	if (endgame_gate_A2(bi) != a2_naive) fail("endgame_gate_A2 != naive", b, turn);

	// --- (3) G_T の等価性
	if (endgame_tall_le1(b) != gate_T_naive(b)) fail("endgame_tall_le1 != naive column count", b, turn);

	// --- (5) 本番 endgame_value() の符号が参照実装 ruleR2 と一致
	const ull rMe_raw = Board::reach(b.Me), rYou_raw = Board::reach(b.You);
	const int ev = endgame_value(b, turn, rMe_raw, rYou_raw);
	const int pred = (ev > 0) - (ev < 0);
	const int ref = ruleR2_ref(b, turn);
	if (pred != ref) fail("endgame_value sign != ruleR2 reference", b, turn);
	if (ev != 0 && (ev != EG_WIN && ev != -EG_WIN)) fail("endgame_value magnitude != +-(INF-100000)", b, turn);

	// --- (2) USE_ENDGAME_R2=1 の葉評価経路(reach_layer_intersection_t)も同じ値を返すか
	if (turn >= 60)
	{
		const Color now = ((turn - 1) & 1) ? Color::White : Color::Black;
		const ull rMe = rMe_raw & ~b.You, rYou = rYou_raw & ~b.Me;
		const int lv = reach_layer_intersection_t(b, now, rMe, rYou, b.valid_move(), turn, 0, 0);
		if (lv != ev) fail("reach_layer_intersection_t(USE_ENDGAME_R2=1) != endgame_value", b, turn);
		n_r2eval++;
	}

	// --- (1) ゲート通過局面での厳密性
	const int exact = solve(b);
	tally(t.r0, ruleR0_ref(b, turn), exact);
	tally(t.r2, ref, exact);
	if (endgame_gate(bi, turn))
	{
		t.pass++;
		tally(t.gated, pred, exact);
	}
}

int main(int argc, char **argv)
{
	init_lines();
	init_sq_lines();
	const long long trials = argc > 1 ? atoll(argv[1]) : 1000000;

	for (long long it = 0; it < trials; it++)
	{
		Board b;
		for (int turn = 1; turn <= TMAX; turn++)
		{
			ull hand = b.valid_move();
			if (!hand) break;
			const ull rMe = Board::reach(b.Me) & ~b.You;
			if (hand & rMe) break;                                  // 即勝ち手あり → 探索はここで打ち切る
			const ull rYou = Board::reach(b.You) & ~b.Me;
			if (!(hand & rYou) && turn >= TMIN) examine(b, turn);    // 制約(C) 成立 = 葉候補
			if (hand & rYou) hand &= rYou;                          // 阻止手に強制
			int k = (int)(rng() % __builtin_popcountll(hand));
			ull h = hand;
			while (k--) h &= h - 1;
			b = b.place_fast_clone(h & -h);
		}
	}

	printf("playouts = %lld\n", trials);
	printf("SSE2 = %d\n", EG_USE_SSE2);
	printf("検査した局面数 = %lld (うち評価関数経路 turn>=60 の照合 = %lld)\n\n", n_checked, n_r2eval);

	printf("[本番 endgame_gate() を通過した局面での本番 endgame_value() の厳密性]\n");
	printf("%5s %10s %10s %8s | %8s %10s %10s %8s\n",
	       "turn", "標本数", "通過数", "通過率", "一致", "取りこぼし", "誤断定", "決定数");
	long long tot_miss = 0, tot_bad = 0;
	for (int t = TMAX; t >= 59; t--)
	{
		const TurnData &d = TD[t];
		if (!d.samples) continue;
		printf("%5d %10lld %10lld %7.1f%% | %8lld %10lld %10lld %8lld\n",
		       t, d.samples, d.pass, 100.0 * d.pass / d.samples,
		       d.gated.ok, d.gated.miss, d.gated.bad, d.gated.decided);
		tot_miss += d.gated.miss; tot_bad += d.gated.bad;
	}
	printf("  合計: 取りこぼし %lld 件 / 誤断定 %lld 件\n", tot_miss, tot_bad);

	printf("\n[turn<=58 は endgame_gate() が常に false であることの確認]\n");
	for (int t = 58; t >= TMIN; t--)
		if (TD[t].samples) printf("  turn %d : 標本 %lld / 通過 %lld\n", t, TD[t].samples, TD[t].pass);

	printf("\n[葉評価の精度比較(ゲート無し・全標本)。R0 = 現行 / R2 = 本実装]\n");
	printf("%5s %10s | %-30s | %-30s\n", "turn", "標本数", "R0 (現行)", "R2 (本実装)");
	for (int t = TMAX; t >= TMIN; t--)
	{
		const TurnData &d = TD[t];
		if (!d.samples) continue;
		printf("%5d %10lld | ok%9lld miss%8lld bad%6lld | ok%9lld miss%8lld bad%6lld\n",
		       t, d.samples, d.r0.ok, d.r0.miss, d.r0.bad, d.r2.ok, d.r2.miss, d.r2.bad);
	}

	printf("\n=== 結果: ");
	if (tot_miss == 0 && tot_bad == 0) printf("合格(ゲート通過局面での取りこぼし・誤断定ともに 0 件)\n");
	else { printf("不合格\n"); return 1; }
	return 0;
}
