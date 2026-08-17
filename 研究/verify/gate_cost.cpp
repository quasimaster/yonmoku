// ゲート判定(2石+空き2 ラインの有無)を評価関数に足したときの計算コストを実測する。
//
// 比較対象:
//   V0 現行の turn>=60 分岐相当(段パリティ規則のみ)
//   V1 V0 + ゲートを cnt[76] の素朴なループで判定
//   V2 V0 + ゲートを cnt64[10] の SWAR(hasvalue)で判定
//   V3 V0 + ゲートを SSE2(_mm_cmpeq_epi8)で判定
//   V4 V0 + ゲートを増分維持済みビットマスクの参照で判定(探索側で維持する前提)
//   VL ライン走査を popcount でやり直す最悪版(cnt[] を使わない場合)
//   VR 参考: Board::reach() ×2(探索が葉で必ず払っているコスト)
//
// ビルド: g++ -O2 -std=c++17 -DNDEBUG -o gate_cost.exe gate_cost.cpp
#include <emmintrin.h>
#include "../../code/common.hpp"
#include "../../code/board.hpp"
#include "../../code/board_inc.hpp"

typedef unsigned long long ull;
static const ull M2 = 0x00000000ffff0000uLL;
static const ull M3 = 0x0000ffff00000000uLL;
static const ull M4 = 0xffff000000000000uLL;

// ---------------------------------------------------------------- 評価本体(V0)
static inline int eval_R2(Color now, ull rMe, ull rYou)
{
	const ull rMe_tmp = rMe;
	rMe = rMe & ~(rYou << 16);
	rYou = rYou & ~(rMe_tmp << 16);
	const ull inter3 = (rMe & rYou) & M3;
	rMe ^= inter3; rYou ^= inter3;
	const ull rB = (now == Color::Black) ? rMe : rYou;
	const ull rW = (now == Color::Black) ? rYou : rMe;
	int v = 0;
	if      (rW & M2)             v = -1;
	else if ((rB & M3) || inter3) v = +1;
	else if (rW & M4)             v = -1;
	return now == Color::Black ? v : -v;
}

// ---------------------------------------------------------------- ゲート実装いろいろ
static inline bool gate_scalar(const unsigned char *cnt)
{
	for (int i = 0; i < LINES_NUM; i++)
		if (cnt[i] == 0x20 || cnt[i] == 0x02) return false;
	return true;
}

#define HASZERO(v)     (((v) - 0x0101010101010101uLL) & ~(v) & 0x8080808080808080uLL)
#define HASVALUE(x, n) HASZERO((x) ^ (0x0101010101010101uLL * (n)))

static inline bool gate_swar(const ull *cnt64)
{
	ull acc = 0;
	for (int i = 0; i < 10; i++)
		acc |= HASVALUE(cnt64[i], 0x20) | HASVALUE(cnt64[i], 0x02);
	return acc == 0;
}

static inline bool gate_sse(const unsigned char *cnt)
{
	const __m128i a = _mm_set1_epi8(0x20), b = _mm_set1_epi8(0x02);
	__m128i acc = _mm_setzero_si128();
	for (int i = 0; i < 80; i += 16)
	{
		const __m128i v = _mm_loadu_si128((const __m128i *)(cnt + i));
		acc = _mm_or_si128(acc, _mm_or_si128(_mm_cmpeq_epi8(v, a), _mm_cmpeq_epi8(v, b)));
	}
	return _mm_movemask_epi8(acc) == 0;
}

// G_A2 用: バイトが {0x01,0x02,0x10,0x20} のいずれかなら不通過(比較 4 本)
static inline bool gate_sse_A2(const unsigned char *cnt)
{
	const __m128i a = _mm_set1_epi8(0x20), b = _mm_set1_epi8(0x02);
	const __m128i c = _mm_set1_epi8(0x10), d = _mm_set1_epi8(0x01);
	__m128i acc = _mm_setzero_si128();
	for (int i = 0; i < 80; i += 16)
	{
		const __m128i v = _mm_loadu_si128((const __m128i *)(cnt + i));
		acc = _mm_or_si128(acc, _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, a), _mm_cmpeq_epi8(v, b)),
		                                     _mm_or_si128(_mm_cmpeq_epi8(v, c), _mm_cmpeq_epi8(v, d))));
	}
	return _mm_movemask_epi8(acc) == 0;
}

static inline bool gate_incremental(ull m0, ull m1) { return (m0 | m1) == 0; }

// 増分維持版 place_fast_clone: 「2石+空き2」ラインのビットマスクも一緒に更新する。
// 述語 {0x20, 0x02} はニブル交換で不変なので、マスク自体のスワップは不要。
struct BoardInc2
{
	BoardInc bi;
	ull two[2];

	BoardInc2 place_fast_clone(unsigned long long bit) const
	{
		BoardInc2 r = *this;
		r.bi.b.Me |= bit;
		swap(r.bi.b.Me, r.bi.b.You);
		const int sq = __builtin_ctzll(bit);
		for (const unsigned char *p = SQ_LINES[sq]; *p != 0xFF; p++)
		{
			const int l = *p;
			const unsigned char c = (r.bi.cnt[l] += 0x10);
			const ull m = 1uLL << (l & 63);
			if (c == 0x20 || c == 0x02) r.two[l >> 6] |=  m;
			else                        r.two[l >> 6] &= ~m;
		}
		for (int i = 0; i < 10; i++)
			r.bi.cnt64[i] = (r.bi.cnt64[i] & 0xF0F0F0F0F0F0F0F0uLL) >> 4 | (r.bi.cnt64[i] & 0x0F0F0F0F0F0F0F0FuLL) << 4;
		return r;
	}
};

static inline bool gate_popcount(const Board &b)
{
	for (int i = 0; i < LINES_NUM; i++)
	{
		const int cm = __builtin_popcountll(b.Me & LINES[i]);
		const int cy = __builtin_popcountll(b.You & LINES[i]);
		if ((cm == 2 && cy == 0) || (cy == 2 && cm == 0)) return false;
	}
	return true;
}

// 探索本体(evaluate_board)と同じ強制手処理で終局まで読み切ったときのノード数
static long long g_nodes = 0;
static int count_nodes(const Board &b)
{
	g_nodes++;
	ull hand = b.valid_move();
	if (!hand) return 0;
	const ull rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const ull rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou) hand &= rYou;
	int best = -1;
	while (hand)
	{
		const ull bit = hand & -hand;
		hand ^= bit;
		const int v = -count_nodes(b.place_fast_clone(bit));
		if (v > best) best = v;
	}
	return best;
}

// ---------------------------------------------------------------- 標本
static const int NPOS = 8192;
static BoardInc POS[NPOS];
static ull RME[NPOS], RYOU[NPOS];
static Color NOW[NPOS];
static ull INCMASK[NPOS][2];
static BoardInc2 POS2[NPOS];
static int npos = 0;

static void collect(int target_turn)
{
	while (npos < NPOS)
	{
		Board b;
		for (int turn = 1; turn <= target_turn; turn++)
		{
			ull hand = b.valid_move();
			if (!hand) break;
			const ull rMe = Board::reach(b.Me) & ~b.You;
			if (hand & rMe) break;
			const ull rYou = Board::reach(b.You) & ~b.Me;
			if (turn == target_turn && !(hand & rYou))
			{
				POS[npos] = BoardInc::from(b);
				RME[npos] = rMe; RYOU[npos] = rYou;
				NOW[npos] = ((turn - 1) & 1) ? Color::White : Color::Black;
				INCMASK[npos][0] = INCMASK[npos][1] = 0;
				for (int i = 0; i < LINES_NUM; i++)
					if (POS[npos].cnt[i] == 0x20 || POS[npos].cnt[i] == 0x02)
						INCMASK[npos][i >> 6] |= 1uLL << (i & 63);
				POS2[npos].bi = POS[npos];
				POS2[npos].two[0] = INCMASK[npos][0];
				POS2[npos].two[1] = INCMASK[npos][1];
				npos++;
				break;
			}
			if (hand & rYou) hand &= rYou;
			int k = (int)(rng() % __builtin_popcountll(hand));
			ull h = hand;
			while (k--) h &= h - 1;
			b = b.place_fast_clone(h & -h);
		}
	}
}

template <typename F>
static double bench(const char *name, long long reps, F f, double base)
{
	// ウォームアップ
	long long sink = 0;
	for (int i = 0; i < npos; i++) sink += f(i);
	const auto t0 = chrono::steady_clock::now();
	for (long long r = 0; r < reps; r++)
		for (int i = 0; i < npos; i++) sink += f(i);
	const auto t1 = chrono::steady_clock::now();
	const double ns = chrono::duration_cast<chrono::nanoseconds>(t1 - t0).count() / (double)(reps * npos);
	if (base > 0) printf("  %-46s %8.2f ns/回   (V0 比 %+7.2f ns, %+6.1f%%)\n", name, ns, ns - base, 100.0 * (ns - base) / base);
	else          printf("  %-46s %8.2f ns/回\n", name, ns);
	if (sink == 0x123456789) printf("");   // 最適化除去よけ
	return ns;
}

int main(int argc, char **argv)
{
	init_lines();
	init_sq_lines();
	const int target_turn = argc > 1 ? atoi(argv[1]) : 60;
	const long long reps = argc > 2 ? atoll(argv[2]) : 4000;
	collect(target_turn);
	printf("turn = %d の局面 %d 個、各 %lld 回反復\n\n", target_turn, npos, reps);

	const double v0 = bench("V0 段パリティ規則のみ(現行 turn>=60 相当)", reps,
	                        [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]); }, 0);
	bench("V1 + ゲート: cnt[76] 素朴ループ", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_scalar(POS[i].cnt); }, v0);
	bench("V2 + ゲート: cnt64[10] SWAR", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_swar(POS[i].cnt64); }, v0);
	bench("V3 + ゲート: SSE2 (cnt 80B を 5 ロード)", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_sse(POS[i].cnt); }, v0);
	bench("V4 + ゲート: 増分維持ビットマスク参照", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_incremental(INCMASK[i][0], INCMASK[i][1]); }, v0);
	bench("V5 + ゲート G_A2: SSE2 (比較 4 本)", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_sse_A2(POS[i].cnt); }, v0);
	bench("VL + ゲート: cnt を使わず popcount 再計算", reps,
	      [](int i) { return eval_R2(NOW[i], RME[i], RYOU[i]) + (int)gate_popcount(POS[i].b); }, v0);

	printf("\n  [参考] 探索が葉で必ず払っているコスト\n");
	bench("VR Board::reach() ×2", reps,
	      [](int i) { return (int)(Board::reach(POS[i].b.Me) + Board::reach(POS[i].b.You)); }, 0);
	const double vp = bench("VP BoardInc::place_fast_clone() 1回", reps,
	      [](int i) { const ull h = POS[i].b.valid_move(); return (int)POS[i].place_fast_clone(h & -h).cnt[0]; }, 0);
	// この局面で探索を打ち切った場合に省けるノード数(= 終局まで読み切るノード数)
	{
		long long nodes = 0;
		for (int i = 0; i < npos; i++) { g_nodes = 0; count_nodes(POS[i].b); nodes += g_nodes; }
		const double per = (double)nodes / npos;
		printf("\n  [参考] この turn で打ち切った場合に省けるノード数: 平均 %.1f ノード\n", per);
		printf("         1ノードあたり概ね reach()×2 = %.1f ns 以上かかるので、節約は概ね %.0f ns/葉\n",
		       35.0, per * 35.0);
	}

	printf("\n  [増分維持を選んだ場合、全ノードで払う追加コスト]\n");
	bench("VP2 マスクも維持する place_fast_clone() 1回", reps,
	      [](int i) { const ull h = POS2[i].bi.b.valid_move(); const BoardInc2 r = POS2[i].place_fast_clone(h & -h); return (int)(r.bi.cnt[0] + (int)r.two[0]); }, vp);
	return 0;
}
