#pragma once

#include "common.hpp"
#include "board.hpp"

// 提案7a: turn の集約(implementation-plan-eval-speedup.md §3.1)。
// evaluate_alpha.hpp の各関数のコピーに turn / turn_bucket を引数で足し、
// 関数先頭の「const int turn = board.turn();」(popcount)と bucket 計算を削除したもの(_t サフィックス)。
// turn >= 60 の早期 return はサブ関数側に残し、条件分岐の構造は変えない。
//
// 本ファイルは現在 evaluate_alpha_inc_tbl.hpp 専用の部品置き場である。
// evaluate_point{fir,sec}_t とエントリ _rt は evaluate_alpha_inc_tbl.hpp の
// evaluate_point{fir,sec}_it / エントリ _rit に置き換わったため削除した。
// 残る 3 関数は _rit から無変更で流用される(evaluate_alpha_inc_tbl.hpp:3)。

// フェーズ1(最終盤の葉評価を規則 R0 → R2 に差し替え)。
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md §3.4
//   0 = 現行の R0(既存ビルドの挙動は完全に不変)
//   1 = 段パリティ定理 + 低段優先の R2(turn=60 で誤断定 4.1% → 1.8%)
// ここは厳密打ち切りのゲートを通らなかった局面が葉に落ちたときに使われる
// 【ヒューリスティック】であり、確定値ではない(確定は endgame_exact.hpp が担う)。
#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 0
#endif

inline int continuous_fir_t(const Board &board, unsigned long long rMe, const unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {3108,1070,674,671};
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[turn_bucket];
}

inline int continuous_sec_t(const Board &board, unsigned long long rMe, const unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {1308,1131,744,698};
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[turn_bucket];
}

inline int reach_layer_intersection_t(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand,
                                      const int turn, const int bucket_fir, const int bucket_sec)
{
	const unsigned long long rMe_tmp = rMe;
	const unsigned long long rMe_esc = rMe & ~(rYou << SIZE * SIZE);//下に相手のリーチがある場合を削除
	const unsigned long long rYou_esc = rYou & ~(rMe_tmp << SIZE * SIZE);//下に相手のリーチがある場合を削除
	rMe = rMe_esc;
	rYou = rYou_esc;

	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;

	const unsigned long long intersection_3 = (rMe & rYou) & mask_3;
	rMe ^= intersection_3;
	rYou ^= intersection_3;

	int sum = 0;

	if(turn >= 60){
#if USE_ENDGAME_R2
		// 規則 R2: 段パリティ定理(黒 = 奇数段 / 白 = 偶数段)+ 低段優先(低い段の脅威が先に発火)。
		// rMe/rYou はエスケープフィルタ適用後。intersection_3 は段3 = 奇数段なので黒側に数える。
		// 判定順 mask_2 → mask_3 → mask_4 が本質(順序を崩すと R0 の欠陥B が再発する)。
		{
			const unsigned long long rB = (now == Color::Black) ? rMe  : rYou;
			const unsigned long long rW = (now == Color::Black) ? rYou : rMe;
			int v = 0;                                             // +1 = 黒勝ち / -1 = 白勝ち
			if      (rW & mask_2)                     v = -1;      // 白の段2(R0 の欠陥A: 白番分岐に無かった)
			else if ((rB & mask_3) || intersection_3) v = +1;      // 黒の段3
			else if (rW & mask_4)                     v = -1;      // 白の段4(R0 の欠陥B: 黒の段3 より先に見ていた)
			if (v) sum = ((now == Color::Black) ? v : -v) * (INF - 100000);
		}
#else
		if(now == Color::Black)
		{
			if(rMe & mask_3 || intersection_3) sum = INF - 100000;
			else if(rYou & mask_2 || rYou & mask_4) sum = - INF + 100000;
		}
		else
		{
			if(rMe & mask_4) sum = INF -100000;
			else if(rYou & mask_3 || intersection_3) sum = - INF + 100000;
		}
#endif
		return sum;
	}

    static const int weightfir[40] = {
		138,476,144,215,209,192,149,-1104,-29,1327,
        177,624,171,314,397,266,341,272,1062,966,
        149,859,124,327,613,258,489,376,567,966,
        164,1467,136,449,985,321,1089,627,1698,-80
    };
    static const int weightsec[40] = {
        231,232,210,151,455,158,345,865,-187,189,
        321,431,284,197,599,180,291,361,152,132,
        298,677,249,175,871,131,509,357,790,1294,
        506,1288,373,158,1361,91,1058,902,2057,672
    };

	if (now == Color::Black)
	{//first (black) player
		{//Me, first (black) player
			sum += __builtin_popcountll(rMe & mask_2) * weightfir[bucket_fir*10 + 0];//2nd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_3) * weightfir[bucket_fir*10 + 1];//3rd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_4) * weightfir[bucket_fir*10 + 2];//4th layer_intersection_fir
		}
		{//You, second (white) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightfir[bucket_fir*10 + 3];//2nd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_3) * weightfir[bucket_fir*10 + 4];//3rd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_4) * weightfir[bucket_fir*10 + 5];//4th layer_intersection_fir
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if(intersection == 1)
			{//odd, black = Me
				sum += weightfir[bucket_fir*10 + 6];
			}
			else if(intersection == 2)
			{//even, white = You
				sum -= weightfir[bucket_fir*10 + 7];
			}
			else if(intersection == 3)
			sum += weightfir[bucket_fir*10 + 8];
			else if(intersection == 4)
			sum -= weightfir[bucket_fir*10 + 9];
		}
	}
	else
	{//second (white) player
		{//Me, second (white) player
			sum += __builtin_popcountll(rMe & mask_2) * weightsec[bucket_sec*10 + 0];//2nd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_3) * weightsec[bucket_sec*10 + 1];//3rd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_4) * weightsec[bucket_sec*10 + 2];//4th layer_intersection_sec
		}
		{//You, first (black) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightsec[bucket_sec*10 + 3];//2nd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_3) * weightsec[bucket_sec*10 + 4];//3rd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_4) * weightsec[bucket_sec*10 + 5];//4th layer_intersection_sec
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if (intersection == 1)
			{//odd, black = You
				sum -= weightsec[bucket_sec*10 + 6];
			}
			else if(intersection == 2)
			{//even, white = Me
				sum += weightsec[bucket_sec*10 + 7];
			}
			else if(intersection == 3)
			sum -= weightsec[bucket_sec*10 + 8];
			else if(intersection == 4)
			sum += weightsec[bucket_sec*10 + 9];
		}
	}
	return sum;
}
