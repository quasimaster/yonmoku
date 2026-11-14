#pragma once

#include "../code/common.hpp"
#include "../code/board.hpp"

// 先手(fir)・後手(sec)を 1 本にまとめた勾配降下法用の評価関数。
//
// 既存の 2 つの学習コードは、同じ評価関数のうち「自分の手番側の分岐だけ」を
// パラメータ化し、相手手番側は定数で埋めていた。
//   evaluate_gd_alpha.hpp                    : 黒(先手)手番の分岐をパラメータ化
//   yonmoku_gradient_descent_second_alpha.cpp: 白(後手)手番の分岐をパラメータ化
// 学習で参照する局面は fir が record 添字の奇数 = 黒手番、sec が偶数 = 白手番と
// 完全に分かれているため、両方の分岐を同時にパラメータ化しても、
// それぞれの学習が読む要素の値は元のコードと 1 ビットも変わらない。
//
// 本ヘッダの中身は上記 2 ファイルの該当行をそのまま複写したものである。
//   evaluate_point            <- evaluate_gd_alpha.hpp:21-110
//                                (= 後手版 evaluate_pointsec と本文完全一致)
//   continuous                <- evaluate_gd_alpha.hpp:131-136
//   reach_layer_intersection  <- evaluate_gd_alpha.hpp:137-190(黒手番の分岐まで)
//                              + yonmoku_gradient_descent_second_alpha.cpp:994-1025
//                                (白手番の分岐)
//                              + evaluate_gd_alpha.hpp:215-231(turn>=60 以降)
//
// evaluate_gd_alpha.hpp と同名の関数を持つので、衝突を避けて namespace gd に入れる。
namespace gd
{

// 勾配降下法で学習する重み(可変パラメータ)。ps[0..28] との対応は main 側と同一。
inline int pb, pc, pd, pe;//基礎点
inline int pg, ph, pi, pj, pk, pl, pm, pn, po, pr, pt;//layer_me / layer_you / intersection / continuous
inline int ppa, ppb, ppc, ppd, ppe, ppf, ppg;//makeT me
inline int pqa, pqb, pqc, pqd, pqe, pqf, pqg;//makeT you

// evaluate_gd_alpha.hpp:21-110 の evaluate_pointfir と、
// yonmoku_gradient_descent_second_alpha.cpp:840-934 の evaluate_pointsec は
// シグネチャ以外の本文が完全一致する(diff 済み)。よって 1 本にまとめる。
inline int evaluate_point(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
    const unsigned long long rMe_tmp = rMe;
	const unsigned long long rMe_esc = rMe & ~(rYou << SIZE * SIZE);//下に相手のリーチがある場合を削除
	const unsigned long long rYou_esc = rYou & ~(rMe_tmp << SIZE * SIZE);//下に相手のリーチがある場合を削除
	rMe = rMe_esc;
	rYou = rYou_esc;

	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	int sum = 0;
    if(turn <= 59)
    {
	    //static const int weight[9] = {0,-60,-56,-16,0,16,56,60,0};//first
		const int weight[9] = {0,0,pb,pc,0,pd,pe,0,0};//first
	    auto count = board.count();
        for (int v : count) sum += weight[v + 4];

        unsigned long long tMe = 0uLL;
        unsigned long long tYou = 0uLL;
        for(int i = 0; i < LINES_NUM; i++)
        {
            if(count[i] == 2)
            {
                unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
                static const unsigned long long mask_1 = 0x000000000000ffffuLL;
				static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
                static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
				static const unsigned long long mask_4 = 0xffff000000000000uLL;
                unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
				while(floatthree)
				{
					unsigned long long h = floatthree & -floatthree;
					unsigned long long make = two & ~h;//makeT点
                    tMe |= make;
					// unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
					// unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
                	sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * ppa;//one
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * ppb;//two
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * ppc;//three
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * ppd;//four

					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * ppe;//two
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * ppf;//three
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * ppg;//four
					floatthree ^= h;
				}
            }
            else if(count[i] == -2)
            {
                unsigned long long two = ~board.You & LINES[i];
				static const unsigned long long mask_1 = 0x000000000000ffffuLL;
				static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
                static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
				static const unsigned long long mask_4 = 0xffff000000000000uLL;

                unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
				while(floatthree)
				{
					unsigned long long h = floatthree & -floatthree;
					unsigned long long make = two & ~h;
                    tYou |= make;
					// unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
					// unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * pqa;
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * pqb;
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * pqc;
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * pqd;

					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * pqe;//two
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * pqf;//three
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * pqg;//four
					floatthree ^= h;
				}

            }
        }

        sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * ppe;//T_T
        sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * ppf;//T_W
        sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * ppg;//W_T

        sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * pqe;
        sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * pqf;
        sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * pqg;

    }
    return sum;

}


inline int continuous(unsigned long long rMe, const unsigned long long rYou)
{
	rMe &= ~(rYou << SIZE * SIZE);
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * po;
}


inline int reach_layer_intersection(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand)
{

	const int turn = board.turn();// turn number (the number of stones = turn - 1)

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
    if(turn <= 59)
    {
		if (now == Color::Black)
        {//first (black) player
            {//Me, first (black) player
                sum += __builtin_popcountll(rMe & mask_2) * pg;//2nd layer_intersection_fir
                sum += __builtin_popcountll(rMe & mask_3) * ph;//3rd layer_intersection_fir
                sum += __builtin_popcountll(rMe & mask_4) * pi;//4th layer_intersection_fir
            }
            {//You, second (white) player
                sum -= __builtin_popcountll(rYou & mask_2) * pj;//2nd layer_intersection_fir
                sum -= __builtin_popcountll(rYou & mask_3) * pk;//3rd layer_intersection_fir
                sum -= __builtin_popcountll(rYou & mask_4) * pl;//4th layer_intersection_fir
            }
            if (intersection_3)
            {//if there exists intersections of reaches on 3rd layer
                int intersection = __builtin_popcountll(intersection_3);
                assert(intersection < 5);
                //if (__builtin_parityll(intersection_3))
                if(intersection == 1)
                {//odd, black = Me
                    sum += pm;
                }
                else if(intersection == 2)
                {//even, white = You
                    sum -= pn;
                }
                else if(intersection == 3)
                sum += pr;
				else if(intersection == 4)
				sum -= pt;

            }
        }
        else
        {//second (white) player
            // ↓ yonmoku_gradient_descent_second_alpha.cpp:996-1025 を字下げのみ揃えて複写。
            //   evaluate_gd_alpha.hpp ではここが定数(48/140/11/64/200/16/-100/+140)だった。
            {//Me, second (white) player
                sum += __builtin_popcountll(rMe & mask_2) * pg;//2nd layer_intersection_sec
                sum += __builtin_popcountll(rMe & mask_3) * ph;//3rd layer_intersection_sec
                sum += __builtin_popcountll(rMe & mask_4) * pi;//4th layer_intersection_sec
            }
            {//You, first (black) player
                sum -= __builtin_popcountll(rYou & mask_2) * pj;//2nd layer_intersection_sec
                sum -= __builtin_popcountll(rYou & mask_3) * pk;//3rd layer_intersection_sec
                sum -= __builtin_popcountll(rYou & mask_4) * pl;//4th layer_intersection_sec
            }
            if (intersection_3)
            {//if there exists intersections of reaches on 3rd layer
                int intersection = __builtin_popcountll(intersection_3);
                assert(intersection < 5);
                //if (__builtin_parityll(intersection_3))
                if(intersection == 1)
                {//odd, black = Me
                    sum -= pm;
                }
                else if(intersection == 2)
                {//even, white = You
                    sum += pn;
                }
                else if(intersection == 3)
                sum -= pr;
					else if(intersection == 4)
					sum += pt;
                
            }
        }
    }
	else if(turn >= 60)
	{
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
	}
	return sum;
}


// 学習で使う特徴量。evaluate_gd_alpha.hpp:316-323 の
// evaluate_pointfir_cont_layer_intersection および
// yonmoku_gradient_descent_second_alpha.cpp:1138-1145 の
// evaluate_pointsec_cont_layer_intersection と同一の式。
inline int evaluate_feature(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	// Board がグローバル名前空間にあるため、ADL で evaluate_gd_alpha.hpp 側の同名関数も
	// 候補に入ってしまう。両方を include しても曖昧にならないよう gd:: で明示する。
	return gd::evaluate_point(board, rMe, rYou) + gd::continuous(rMe, rYou) - gd::continuous(rYou, rMe) + gd::reach_layer_intersection(board, now, rMe, rYou, hand);
}

// ps[0..28] を上のパラメータ群へ配る。特徴量行列 A の構築と重み出力で共有する。
inline void set_parameters(const int ps[29])
{
	pb = ps[0], pc = ps[1], pd = ps[2], pe = ps[3];//基礎点
	pg = ps[4], ph = ps[5], pi = ps[6];//layer_me
	pj = ps[7], pk = ps[8], pl = ps[9];//leyer_you
	pm = ps[10], pn = ps[11], pr = ps[12], pt = ps[13];//intersection
	po = ps[14];//continuous
	ppa = ps[15], ppb = ps[16], ppc = ps[17], ppd = ps[18];//nonfloat_makeT me
	pqa = ps[19], pqb = ps[20], pqc = ps[21], pqd = ps[22];//nonfloat_makeT you
	ppe = ps[23], ppf = ps[24], ppg = ps[25];//float_make me
	pqe = ps[26], pqf = ps[27], pqg = ps[28];//float_make you
}

}// namespace gd