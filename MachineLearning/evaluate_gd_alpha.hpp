#pragma once

#include "../code/common.hpp"
#include "../code/board.hpp"

// 勾配降下法で学習する評価関数の重み（可変パラメータ）。
// 特徴量行列 A の構築時に「あるパラメータだけ 1、他は 0」に設定して
// 評価関数を呼び、各パラメータの寄与を線形分解する。
inline int pb, pc, pd, pe;//基礎点
inline int pg, ph, pi, pj, pk, pl, pm, pn, po, pr, pt;//layer_me / layer_you / intersection / continuous
inline int ppa, ppb, ppc, ppd, ppe, ppf, ppg;//makeT me
inline int pqa, pqb, pqc, pqd, pqe, pqf, pqg;//makeT you

inline int evaluate(const Board &board)
{
	int sum = 0;
	for (int v : board.count()) sum += v;
	return sum;
}

inline int evaluate_pointfir(const Board &board, unsigned long long rMe, unsigned long long rYou)
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

inline int evaluate_pointsec(const Board &board)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
    int sum = 0;
    if(turn <= 59)
    {
	    static const int weight[9] = {0,-60,-56,-16,0,16,56,60,0};//second
	    for (int v : board.count()) sum += weight[v + 4];
    }
	return sum;
}

inline int evaluate_random(const Board &board)
{
	//int sum = 0;
	//static const int weight[9] = {0,0,0,0,0,0,0,0,0};
	//for (int v : board.count()) sum += weight[v + 4];
	return 0;
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
            {//Me, second (white) player
                sum += __builtin_popcountll(rMe & mask_2) * 48;//2nd layer_intersection_sec
                sum += __builtin_popcountll(rMe & mask_3) * 140;//3rd layer_intersection_sec
                sum += __builtin_popcountll(rMe & mask_4) * 11;//4th layer_intersection_sec
            }
            {//You, first (black) player
                sum -= __builtin_popcountll(rYou & mask_2) * 64;//2nd layer_intersection_sec
                sum -= __builtin_popcountll(rYou & mask_3) * 200;//3rd layer_intersection_sec
                sum -= __builtin_popcountll(rYou & mask_4) * 16;//4th layer_intersection_sec
            }
            if (intersection_3)
            {//if there exists intersections of reaches on 3rd layer
                if (__builtin_parityll(intersection_3))
                {//odd, black = You
                    sum -= 100;
                }
                else
                {//even, white = Me
                    sum += 140;
                }
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

inline int reach_layer(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand)
{
	const unsigned long long rMe_tmp = rMe & ~(hand | rYou << SIZE * SIZE);
	const unsigned long long rYou_tmp = rYou & ~(hand | rMe << SIZE * SIZE);
	rMe = rMe_tmp, rYou = rYou_tmp;
	//rMe &= ~hand;
	//rYou &= ~hand;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;

	const int turn = board.turn();// turn number (the number of stones = turn - 1)

	int sum = 0;
	if(turn <= 59)
	{
		if (now == Color::Black)
		{//first (black) player
			{//Me, first (black) player
				sum += __builtin_popcountll(rMe & mask_2) * 48;//2nd layer_fir
				sum += __builtin_popcountll(rMe & mask_3) * 140;//3rd layer_fir
				sum += __builtin_popcountll(rMe & mask_4) * 11;//4th layer_fir
			}
			{//You, second (white) player
				sum -= __builtin_popcountll(rYou & mask_2) * 64;//2nd layer_fir
				sum -= __builtin_popcountll(rYou & mask_3) * 140;//3rd layer_fir
				sum -= __builtin_popcountll(rYou & mask_4) * 16;//4th layer_fir
			}
		}
		else
		{//second (white) player
			{//Me, second (white) player
				sum += __builtin_popcountll(rMe & mask_2) * 48;//2nd layer_sec
				sum += __builtin_popcountll(rMe & mask_3) * 64;//3rd layer_sec
				sum += __builtin_popcountll(rMe & mask_4) * 16;//4th layer_sec
			}
			{//You, first (black) player
				sum -= __builtin_popcountll(rYou & mask_2) * 64;//2nd layer_sec
				sum -= __builtin_popcountll(rYou & mask_3) * 48;//3rd layer_sec
				sum -= __builtin_popcountll(rYou & mask_4) * 16;//4th layer_sec
			}
		}
	}
	else if(turn >= 60)
	{
		if(now == Color::Black)
		{
			if(rMe & mask_3) sum = INF - 100000;
			else if(rYou & mask_2 | rYou & mask_4) sum = - INF + 100000;
		}
		else
		{
			if(rMe & mask_4) sum = INF -100000;
			else if(rYou & mask_3) sum = - INF + 100000;
		}
	}
	return sum;
}

inline int evaluate_cont(const Board &board)
{
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	return evaluate(board) + continuous(rMe, rYou) - continuous(rYou, rMe);
}

inline int evaluate_layer(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate(board) + reach_layer(board,now, rMe, rYou, hand);
}

inline int evaluate_pointfir_cont_layer(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointfir(board, rMe, rYou) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer(board,now, rMe, rYou, hand);
}

inline int evaluate_pointfir_cont_layer_intersection(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointfir(board, rMe, rYou) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
}

inline int evaluate_pointsec_cont_layer(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointsec(board) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer(board,now, rMe, rYou, hand);
}

inline int evaluate_pointsec_cont_layer_intersection(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointsec(board) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
}

inline int evaluate_pointfir_layer_intersection(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointfir(board, rMe, rYou) + reach_layer_intersection(board,now, rMe, rYou, hand);
}
