#pragma once

#include "evaluate_alpha_inc_tbl_w.hpp"   // continuous_*_t / reach_layer_intersection_t / flag_tbl(無変更で流用)
#include "board_inc2.hpp"                 // BoardInc2 / USE_FIXCNT
#include "eval_weights_core2.hpp"         // EvalWeightsCore2 / flag_tbl_sw

#if defined(__SSE2__) || defined(_M_X64) || defined(_M_AMD64)
  #include <emmintrin.h>
  #define EVAL2_USE_SSE2 1
#else
  #define EVAL2_USE_SSE2 0
#endif

// evaluate_alpha_inc_tbl_w.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md §4.1 / §4.3)。
// 評価値は流用元と完全に同一で、76 ライン走査の「回し方」と「表の選び方」だけを変える。
//
//   USE_EVALSEL = 1 : (1) stdweight の加算だけを 76 ライン分、分岐なしで回し、
//                     (2) makeT 検出に入るライン(v == ±2 ⇔ cnt == 0x20 / 0x02)を SSE2 の比較で抽出して、そのラインだけ処理する。
//                     流用元は 76 ラインごとに flag_tbl を引いて分岐しており、±2 ラインの出現位置が局面依存で分岐予測が外れやすい。
//                     sum は整数加算、tMe/tYou は OR の蓄積なので、処理順が変わっても値は同じ。
//   USE_EVALSEL = 0 : 流用元と同じ 1 ループ(A/B 用)。
//   USE_FIXCNT  = 1 : 白番ノード(Me = 白)では BoardInc2::cnt の向きが逆なので、ニブル交換済みの表(_sw)と比較値(0x02/0x20)を使う。
//
// fir / sec の 2 関数は「使う重み(fir/sec)」以外は同一なので、テンプレートで 1 本にまとめてある(流用元は 2 本を手書き)。
#ifndef USE_EVALSEL
#define USE_EVALSEL 1
#endif
#if USE_EVALSEL && !EVAL2_USE_SSE2
#error "USE_EVALSEL=1 requires SSE2 (x86-64 baseline). Build with -DUSE_EVALSEL=0 on this target."
#endif

#if USE_EVALSEL
// cnt[80] の中で値が c に等しいライン番号のビットマスク(0..63 → lo、64..79 → hi。76..79 はパディング 0 で一致しない)
inline void eval2_select_lines(const unsigned char* cnt, unsigned char c, unsigned long long& lo, unsigned& hi)
{
	const __m128i cc = _mm_set1_epi8((char)c);
	lo = 0;
	for (int i = 0; i < 64; i += 16)
		lo |= (unsigned long long)(unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(_mm_loadu_si128((const __m128i*)(cnt + i)), cc)) << i;
	hi = (unsigned)_mm_movemask_epi8(_mm_cmpeq_epi8(_mm_loadu_si128((const __m128i*)(cnt + 64)), cc));
}
#endif

template<bool SEC>
inline int evaluate_point_it2(const BoardInc2 &board, unsigned long long rMe, unsigned long long rYou,
                              const int turn, const int turn_bucket, const EvalWeightsCore2 &W)
{
	if(turn >= 60){
		return 0;
	}

	int sum = 0;

	// 流用元の巻き上げと同一(maketweight[bucket*8 + k] / conti_maketweight[bucket*6 + k])
	const SideWeights& S = SEC ? W.base.sec : W.base.fir;
	const int* const mw = S.maketweight       + turn_bucket * 8;
	const int* const cw = S.conti_maketweight + turn_bucket * 6;

	// stdweight 表と ±2 判定表。USE_FIXCNT なら白番ノードだけニブル交換済みの表を引く
#if USE_FIXCNT
	const bool swp = ((turn - 1) & 1) != 0;                    // 白番(= Me が白)なら cnt の向きが Me/You と逆
	const int* const sw = swp ? (SEC ? W.stdweight_sec_tbl_sw      : W.stdweight_fir_tbl_sw)[turn_bucket]
	                          : (SEC ? W.base.stdweight_sec_tbl    : W.base.stdweight_fir_tbl)[turn_bucket];
	const unsigned char* const ft = swp ? flag_tbl_sw : flag_tbl;
	const unsigned char cME = swp ? 0x02 : 0x20, cYOU = swp ? 0x20 : 0x02;   // v == +2 / -2 に当たる cnt 値
#else
	const int* const sw = (SEC ? W.base.stdweight_sec_tbl : W.base.stdweight_fir_tbl)[turn_bucket];
	const unsigned char* const ft = flag_tbl;
	const unsigned char cME = 0x20, cYOU = 0x02;
#endif
	(void)ft; (void)cME; (void)cYOU;

	static const unsigned long long mask_1 = 0x000000000000ffffuLL;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;
	unsigned long long tMe = 0uLL;
	unsigned long long tYou = 0uLL;

	// makeT 検出本体。中身は流用元 evaluate_point{fir,sec}_it の分岐内と同一
	auto body_me = [&](const int i)
	{//v == +2: makeT 検出 Me 側
		unsigned long long two = ~board.b.Me & LINES[i];//LINE内の玉が入っていない部分
		unsigned long long floatthree = two & mask_3 & ~((rYou | board.b.Me | board.b.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
		while(floatthree)
		{
			unsigned long long h = floatthree & -floatthree;
			unsigned long long make = two & ~h;//makeT点
			tMe |= make;
			sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * mw[0];
			sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * mw[1];
			sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * mw[2];
			sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * mw[3];
			floatthree ^= h;
		}
	};
	auto body_you = [&](const int i)
	{//v == -2: makeT 検出 You 側
		unsigned long long two = ~board.b.You & LINES[i];
		unsigned long long floatthree = two & mask_3 & ~((rMe | board.b.Me | board.b.You) << SIZE * SIZE);
		while(floatthree)
		{
			unsigned long long h = floatthree & -floatthree;
			unsigned long long make = two & ~h;
			tYou |= make;
			sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * mw[4];
			sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * mw[5];
			sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * mw[6];
			sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * mw[7];
			floatthree ^= h;
		}
	};

#if USE_EVALSEL
	// (1) stdweight は 76 ライン分を分岐なしで加算
	for(int i = 0; i < LINES_NUM; i++) sum += sw[board.cnt[i]];
	// (2) makeT 候補(v == ±2)のラインだけ SSE2 で拾って処理(順序が変わっても sum / tMe / tYou は同じ値になる)
	{
		unsigned long long lo; unsigned hi;
		eval2_select_lines(board.cnt, cME, lo, hi);
		while(lo) { body_me(__builtin_ctzll(lo));      lo &= lo - 1; }
		while(hi) { body_me(64 + __builtin_ctz(hi));   hi &= hi - 1; }
		eval2_select_lines(board.cnt, cYOU, lo, hi);
		while(lo) { body_you(__builtin_ctzll(lo));     lo &= lo - 1; }
		while(hi) { body_you(64 + __builtin_ctz(hi));  hi &= hi - 1; }
	}
#else
	// 流用元と同じ 1 ループ
	for(int i = 0; i < LINES_NUM; i++)
	{
		const unsigned b = board.cnt[i];
		sum += sw[b];
		if(ft[b] & 1)      body_me(i);
		else if(ft[b] & 2) body_you(i);
	}
#endif

	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * cw[0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * cw[1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * cw[2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * cw[3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * cw[4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * cw[5];
	return sum;
}

// エントリ(_rit2)。流用元 _rit と同一構造で、BoardInc2 / EvalWeightsCore2 を取る。
inline int evaluate_pointfir_cont_layer_intersection_rit2(
	const BoardInc2 &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand,
	const EvalWeightsCore2 &W)
{
	assert(board_inc2_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_point_it2<false>(board, rMe, rYou, turn, bucket_fir, W)
	     + continuous_fir_t(board.b, rMe, rYou, turn, bucket_fir, W.base.fir)
	     - continuous_fir_t(board.b, rYou, rMe, turn, bucket_fir, W.base.fir)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec, W.base);
}

inline int evaluate_pointsec_cont_layer_intersection_rit2(
	const BoardInc2 &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand,
	const EvalWeightsCore2 &W)
{
	assert(board_inc2_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_point_it2<true>(board, rMe, rYou, turn, bucket_sec, W)
	     + continuous_sec_t(board.b, rMe, rYou, turn, bucket_sec, W.base.sec)
	     - continuous_sec_t(board.b, rYou, rMe, turn, bucket_sec, W.base.sec)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec, W.base);
}
