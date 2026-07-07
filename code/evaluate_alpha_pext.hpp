#pragma once

#include "evaluate_alpha_t.hpp"

// 提案7b: pext + 256 エントリテーブル(implementation-plan-eval-speedup.md §3.2)。
// 7a(evaluate_alpha_t.hpp)に対し、evaluate_point{fir,sec}_t 内の
// 「board.count() + stdweight 総和 + ±2 判定」を pext とテーブル参照に置き換える(_p / _rp サフィックス)。
// makeT 検出の while ループ本体・重み・tMe/tYou の集約は 7a と同一。評価値は完全一致する。
// 要 BMI2(ビルドは -march=native)。非対応ビルドでは 7a の実装にフォールバックする。

#if defined(__BMI2__)
#include <immintrin.h>   // _pext_u64
#define EVAL_PEXT_ENABLED 1
#else
#define EVAL_PEXT_ENABLED 0
#endif

// init_eval_tables() で事前計算(main の init_lines() の後に呼ぶ)
// idx = pext(Me, LINE) << 4 | pext(You, LINE) の 256 通り。合計約 8.5KB で L1 に収まる。
alignas(64) inline int stdweight_fir_tbl[4][256];   // [turn_bucket][idx] → stdweight 寄与
alignas(64) inline int stdweight_sec_tbl[4][256];
alignas(64) inline unsigned char flag_tbl[256];     // bit0: count==+2(Me のみ2石), bit1: count==-2(You のみ2石)

inline void init_eval_tables()
{
	// evaluate_point{fir,sec} の stdweight(値は evaluate_alpha.hpp:14-19, 114-119 と同一)
	static const int stdweight_fir[28] = {
		0,-58,-20,0,27,57,0,
		0,-58,-20,0,27,57,0,
		0,-86,-9,0,22,56,0,
		0,-96,-31,-10,29,0
	};
	static const int stdweight_sec[28] = {
		0,-52,-22,0,28,65,0,
		0,-70,-24,0,30,99,0,
		0,-33,-5,0,20,97,0,
		0,-2,11,0,27,122,0
	};
	for (int idx = 0; idx < 256; idx++)
	{
		const int me4 = idx >> 4, you4 = idx & 15;
		const int cme = __builtin_popcount(me4), cyou = __builtin_popcount(you4);
		const int v = (cme && cyou) ? 0 : (cme ? cme : -cyou);   // board.count() と同じ規約(両者混在は 0)
		// |v| == 4 は勝敗確定済みラインで評価中には現れないが、テーブルは全 idx を埋めるため
		// ±3 に丸めて構築する(stdweight の両端は 0 なので値も一致する)
		const int vc = max(-3, min(3, v));
		for (int b = 0; b < 4; b++)
		{
			stdweight_fir_tbl[b][idx] = stdweight_fir[b * 7 + vc + 3];
			stdweight_sec_tbl[b][idx] = stdweight_sec[b * 7 + vc + 3];
		}
		flag_tbl[idx] = (unsigned char)((v == 2 ? 1 : 0) | (v == -2 ? 2 : 0));
	}
}

#if EVAL_PEXT_ENABLED

inline int evaluate_pointfir_p(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}

	int sum = 0;

	static const int maketweight[32] = {
		-80,-38,45,0,5,-33,26,14,
		117,-62,68,27,52,-58,38,14,
		179,-53,120,78,109,-18,44,30,
		287,-176,139,100,248,-17,48,20
	};

	static const int conti_maketweight[24] = {
		109,143,384,66,119,174,
		203,252,52,80,101,64,
		362,648,100,135,294,28,
		689,1192,84,304,518,-169
	};

	static const unsigned long long mask_1 = 0x000000000000ffffuLL;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;
    unsigned long long tMe = 0uLL;
    unsigned long long tYou = 0uLL;
	// ★7b: board.count() の実体化を排し、pext + テーブル参照で stdweight 総和と ±2 判定を同時に行う
	for(int i = 0; i < LINES_NUM; i++)
	{
		const unsigned idx = (unsigned)(_pext_u64(board.Me, LINES[i]) << 4 | _pext_u64(board.You, LINES[i]));
		sum += stdweight_fir_tbl[turn_bucket][idx];
		if(flag_tbl[idx] & 1)
		{//count == +2: makeT 検出 Me 側(中身は 7a と同一。two は分岐内で計算)
			unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//makeT点
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];
				floatthree ^= h;
			}
		}
		else if(flag_tbl[idx] & 2)
		{//count == -2: makeT 検出 You 側
			unsigned long long two = ~board.You & LINES[i];
			unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;
                tYou |= make;
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket *8 + 4];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket *8 + 5];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket *8 + 6];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket *8 + 7];
				floatthree ^= h;
			}
		}
	}
	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 5];
    return sum;
}

inline int evaluate_pointsec_p(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	int sum = 0;

	static const int maketweight[32] = {
		8,-56,25,1,105,-12,44,20,
		30,-47,34,7,112,-49,65,39,
		79,-27,54,30,206,-57,126,84,
		516,-93,33,0,424,-161,123,89
	};

	static const int conti_maketweight[24]{
		85,90,100,72,110,345,
		78,98,14,171,206,101,
		135,312,-4,421,694,139,
		317,427,-268,861,1411,188
	};

	static const unsigned long long mask_1 = 0x000000000000ffffuLL;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;
    unsigned long long tMe = 0uLL;
    unsigned long long tYou = 0uLL;
	for(int i = 0; i < LINES_NUM; i++)
	{
		const unsigned idx = (unsigned)(_pext_u64(board.Me, LINES[i]) << 4 | _pext_u64(board.You, LINES[i]));
		sum += stdweight_sec_tbl[turn_bucket][idx];
		if(flag_tbl[idx] & 1)
		{//count == +2
			unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//makeT点
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];
				floatthree ^= h;
			}
		}
		else if(flag_tbl[idx] & 2)
		{//count == -2
			unsigned long long two = ~board.You & LINES[i];
			unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;
                tYou |= make;
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 4];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 5];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 6];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 7];
				floatthree ^= h;
			}
		}
	}
	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 5];
    return sum;
}

#else   // !EVAL_PEXT_ENABLED: BMI2 非対応ビルドでは 7a の実装にフォールバック

inline int evaluate_pointfir_p(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	return evaluate_pointfir_t(board, rMe, rYou, turn, turn_bucket);
}

inline int evaluate_pointsec_p(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	return evaluate_pointsec_t(board, rMe, rYou, turn, turn_bucket);
}

#endif  // EVAL_PEXT_ENABLED

// エントリ(_rp)。7a の _rt と同一構造で、evaluate_point のみ _p 版に差し替える。
// continuous / reach_layer_intersection は 7a の _t 版をそのまま流用する。
inline int evaluate_pointfir_cont_layer_intersection_rp(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const int turn = board.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.player());
	const unsigned long long rMe  = rMe_raw  & ~board.You;
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointfir_p(board, rMe, rYou, turn, bucket_fir)
	     + continuous_fir_t(board, rMe, rYou, turn, bucket_fir)
	     - continuous_fir_t(board, rYou, rMe, turn, bucket_fir)
	     + reach_layer_intersection_t(board, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}

inline int evaluate_pointsec_cont_layer_intersection_rp(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const int turn = board.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.player());
	const unsigned long long rMe  = rMe_raw  & ~board.You;
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointsec_p(board, rMe, rYou, turn, bucket_sec)
	     + continuous_sec_t(board, rMe, rYou, turn, bucket_sec)
	     - continuous_sec_t(board, rYou, rMe, turn, bucket_sec)
	     + reach_layer_intersection_t(board, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}
