#pragma once

#include "evaluate_alpha_t.hpp"
#include "board_inc.hpp"

// 提案7c: BoardInc の充填数配列から評価する評価関数一式(_i / _ri サフィックス)。
// 7a(evaluate_alpha_t.hpp)のコピーに対し、evaluate_point{fir,sec} の
// board.count() を cnt_to_v[board.cnt[i]] のテーブル参照に置き換える。
// makeT 検出・重み・tMe/tYou の集約は 7a と同一。評価値は完全一致する。
// continuous / reach_layer_intersection は Board(board.b)を渡して _t 版を流用する。

// hi ニブル=Me 石数, lo ニブル=You 石数 → board.count() と同じ規約の値
inline signed char cnt_to_v[256];

inline void init_cnt_to_v()
{
	for (int idx = 0; idx < 256; idx++)
	{
		const int cme = idx >> 4, cyou = idx & 15;
		const int v = (cme && cyou) ? 0 : (cme ? cme : -cyou);
		// |v| == 4 は勝敗確定済みラインで評価中には現れないが、±3 に丸めて
		// stdweight の添字範囲に収める(丸め先の重みは 0 で値も一致する)
		cnt_to_v[idx] = (signed char)max(-3, min(3, v));
	}
}

inline int evaluate_pointfir_i(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}

	int sum = 0;
	static const int stdweight[28] = {
		0,-58,-20,0,27,57,0,
		0,-58,-20,0,27,57,0,
		0,-86,-9,0,22,56,0,
		0,-96,-31,-10,29,0
	};

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
	// ★7c: board.count() の代わりに増分維持された充填数 cnt[] を参照する
	for(int i = 0; i < LINES_NUM; i++)
	{
		const int v = cnt_to_v[board.cnt[i]];
		assert(v >= -3 && v <= 3);
		sum += stdweight[turn_bucket * 7 + v + 3];//0~4,5~14,...,45~54
		if(v == 2)
		{
			unsigned long long two = ~board.b.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.b.Me | board.b.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
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
		else if(v == -2)
		{
			unsigned long long two = ~board.b.You & LINES[i];
			unsigned long long floatthree = two & mask_3 & ~((rMe | board.b.Me | board.b.You) << SIZE * SIZE);
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

inline int evaluate_pointsec_i(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	int sum = 0;
	static const int weight[28] = {
		0,-52,-22,0,28,65,0,
		0,-70,-24,0,30,99,0,
		0,-33,-5,0,20,97,0,
		0,-2,11,0,27,122,0
	};

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
		const int v = cnt_to_v[board.cnt[i]];
		assert(v >= -3 && v <= 3);
		sum += weight[turn_bucket * 7 + v + 3];//1~3,4~13,...,44~53
		if(v == 2)
		{
			unsigned long long two = ~board.b.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.b.Me | board.b.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
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
		else if(v == -2)
		{
			unsigned long long two = ~board.b.You & LINES[i];
			unsigned long long floatthree = two & mask_3 & ~((rMe | board.b.Me | board.b.You) << SIZE * SIZE);
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

// エントリ(_ri)。7a の _rt と同一構造で、第1引数を BoardInc にし evaluate_point を _i 版に差し替える。
inline int evaluate_pointfir_cont_layer_intersection_ri(
	const BoardInc &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	assert(board_inc_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_pointfir_i(board, rMe, rYou, turn, bucket_fir)
	     + continuous_fir_t(board.b, rMe, rYou, turn, bucket_fir)
	     - continuous_fir_t(board.b, rYou, rMe, turn, bucket_fir)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}

inline int evaluate_pointsec_cont_layer_intersection_ri(
	const BoardInc &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	assert(board_inc_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_pointsec_i(board, rMe, rYou, turn, bucket_sec)
	     + continuous_sec_t(board.b, rMe, rYou, turn, bucket_sec)
	     - continuous_sec_t(board.b, rYou, rMe, turn, bucket_sec)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}
