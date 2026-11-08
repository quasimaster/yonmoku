// =============================================================================
//  evaluate_alpha_t.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  evaluate_alpha.hpp の関数に、手数 turn と手数の区間 turn_bucket を引数で渡すようにした版(_t)。
//  関数の中で毎回 board.turn()(popcount)と区間を計算し直す手間を省く。計算の式は evaluate_alpha.hpp と同じ(重みの値は ver7.2 で、evaluate_alpha.hpp とは違う)。
//  現在は evaluate_alpha_inc_tbl.hpp の部品置き場で、次の 3関数だけが残っている。
//    continuous_fir_t / continuous_sec_t / reach_layer_intersection_t
//  rB / rW は、色の入れ替えに合わせて rW(白の決勝点)/ rB(黒の決勝点)と名前を入れ替えた。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
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

// 縦に連続する 2つの決勝点の項(evaluate_alpha.hpp の continuous_fir / continuous_sec と同じ)。
// _fir が先手(白)用、_sec が後手(黒)用。
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

// 決勝点の段と重複Tポイントの数の項(evaluate_alpha.hpp の reach_layer_intersection と同じ)。
// bucket_fir / bucket_sec は先手用 / 後手用の手数の区間。turn >= 60 の扱いは USE_ENDGAME_R2 で選ぶ。
inline int reach_layer_intersection_t(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand,
                                      const int turn, const int bucket_fir, const int bucket_sec)
{
	const unsigned long long rMe_tmp = rMe;
	const unsigned long long rMe_esc = rMe & ~(rYou << SIZE * SIZE);//下に相手の決勝点がある場合を削除
	const unsigned long long rYou_esc = rYou & ~(rMe_tmp << SIZE * SIZE);//下に相手の決勝点がある場合を削除
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
		// 規則 R2: 段パリティ定理(白 = 奇数段 / 黒 = 偶数段)+ 低段優先(低い段の脅威が先に発火)。
		// rMe/rYou はエスケープフィルタ適用後。intersection_3 は3段目 = 奇数段なので白側に数える。
		// 判定順 mask_2 → mask_3 → mask_4 が本質(順序を崩すと R0 の欠陥B が再発する)。
		{
			// rW / rB: 白 / 黒の決勝点(手番に関係なく色で持ち直す)。
			const unsigned long long rW = (now == Color::White) ? rMe  : rYou;
			const unsigned long long rB = (now == Color::White) ? rYou : rMe;
			int v = 0;                                             // +1 = 白勝ち / -1 = 黒勝ち
			if      (rB & mask_2)                     v = -1;      // 黒の2段目(R0 の欠陥A: 黒番分岐に無かった)
			else if ((rW & mask_3) || intersection_3) v = +1;      // 白の3段目
			else if (rB & mask_4)                     v = -1;      // 黒の4段目(R0 の欠陥B: 白の3段目より先に見ていた)
			if (v) sum = ((now == Color::White) ? v : -v) * (INF - 100000);
		}
// 規則 R0(既定): evaluate_alpha.hpp と同じ判定。
//   白の手番: 自分に Tポイントか重複Tポイントがあれば勝ち、なければ相手に 2段目か 4段目の決勝点があれば負け。
//   黒の手番: 自分に 4段目の決勝点があれば勝ち、相手に Tポイントか重複Tポイントがあれば負け。
#else
		if(now == Color::White)
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

	if (now == Color::White)
	{//first (white) player
		{//Me, first (white) player
			sum += __builtin_popcountll(rMe & mask_2) * weightfir[bucket_fir*10 + 0];//2nd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_3) * weightfir[bucket_fir*10 + 1];//3rd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_4) * weightfir[bucket_fir*10 + 2];//4th layer_intersection_fir
		}
		{//You, second (black) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightfir[bucket_fir*10 + 3];//2nd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_3) * weightfir[bucket_fir*10 + 4];//3rd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_4) * weightfir[bucket_fir*10 + 5];//4th layer_intersection_fir
		}
		// 重複Tポイントの数による項。奇数個なら白に、偶数個なら黒に有利。
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if(intersection == 1)
			{//odd, white = Me
				sum += weightfir[bucket_fir*10 + 6];
			}
			else if(intersection == 2)
			{//even, black = You
				sum -= weightfir[bucket_fir*10 + 7];
			}
			else if(intersection == 3)
			sum += weightfir[bucket_fir*10 + 8];
			else if(intersection == 4)
			sum -= weightfir[bucket_fir*10 + 9];
		}
	}
	else
	{//second (black) player
		{//Me, second (black) player
			sum += __builtin_popcountll(rMe & mask_2) * weightsec[bucket_sec*10 + 0];//2nd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_3) * weightsec[bucket_sec*10 + 1];//3rd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_4) * weightsec[bucket_sec*10 + 2];//4th layer_intersection_sec
		}
		{//You, first (white) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightsec[bucket_sec*10 + 3];//2nd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_3) * weightsec[bucket_sec*10 + 4];//3rd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_4) * weightsec[bucket_sec*10 + 5];//4th layer_intersection_sec
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if (intersection == 1)
			{//odd, white = You
				sum -= weightsec[bucket_sec*10 + 6];
			}
			else if(intersection == 2)
			{//even, black = Me
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
