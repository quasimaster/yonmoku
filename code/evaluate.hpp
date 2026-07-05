#pragma once

#include "common.hpp"
#include "board.hpp"

inline int evaluate_pointfir(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}

	int sum = 0;
	static const int stdweight[28] = {
		0,-60,-22,0,28,61,0,
		0,-83,-26,0,31,92,0,
		0,-87,-15,0,28,56,0,
		0,-109,-37,0,-5,30,0
	};
	auto count = board.count();
	const int turn_bucket = (turn - 4) / 14;
	for (int v : count){
		assert(v >= -3 && v <= 3);
		sum += stdweight[turn_bucket * 7 + v + 3];//0~4,5~14,...,45~54
	}

	static const int maketweight[32] = {
		-38,-32,52,2,48,-45,32,15,
		158,-54,85,19,80,-45,38,11,
		422,1,143,76,119,10,50,46,
		1009,-90,184,82,165,-26,23,111
	};

	static const int float_maketweight[24] = {
		252,241,72,17,42,22,
		10,294,161,-54,62,47,
		81,488,239,6,109,12,
		105,1002,594,87,113,-39
	};

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
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
				unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
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
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
				unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket *8 + 4];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket *8 + 5];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket *8 + 6];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket *8 + 7];

				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
				floatthree ^= h;
			}

		}
	}
    return sum;

}

inline int evaluate_pointsec(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}
	int sum = 0;
	static const int weight[28] = {
		0,-50,-21,0,25,66,0,
		0,-70,-23,0,29,103,0,
		0,-40,-8,0,26,88,0,
		0,-38,14,0,34,110,0
	};

	auto count = board.count();
	const int turn_bucket = (turn - 5) / 14;
	for (int v : count){
		assert(v >= -3 && v <= 3);
		sum += weight[turn_bucket * 7 + v + 3];//1~3,4~13,...,44~53
	}
	static const int maketweight[32] = {
		46,-57,25,5,90,-6,49,13,
		40,-46,33,1,141,-40,82,36,
		121,10,50,20,414,1,152,99,
		17,-109,-9,-25,1049,-80,169,136
	};

	static const int float_maketweight[24]{
		21,73,9,69,137,67,
		-35,99,52,-19,184,93,
		10,239,120,64,295,71,
		45,355,227,-61,321,-10
	};

	static const unsigned long long mask_1 = 0x000000000000ffffuLL;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;
	for(int i = 0; i < LINES_NUM; i++)
	{
		if(count[i] == 2)
		{
			unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//makeT点
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
				unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(nonfloat_make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
				sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
				floatthree ^= h;
			}
		}
		else if(count[i] == -2)
		{
			unsigned long long two = ~board.You & LINES[i];
			unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
				unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 4];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 5];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 6];
				sum -= __builtin_popcountll(nonfloat_make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 7];

				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
				sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
				floatthree ^= h;
			}
		}
	}
    return sum;
}

inline int evaluate_random(const Board &board)
{
	return 0;
}

inline int continuous_fir(const Board &board, unsigned long long rMe, const unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {2359,982,674,406};
	//assert(turn < 64);
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[(turn - 4) / 14];
}

inline int continuous_sec(const Board &board, unsigned long long rMe, const unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {1203,990,660,408};
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[(turn - 5) / 14];
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

	if(turn >= 60){
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
		return sum;
	}

    static const int weightfir[40] = {
		121,465,142,178,234,186,348,-513,659,1249,
        175,591,169,304,382,239,350,245,-454,569,
        177,820,154,328,624,250,444,318,760,-1109,
        191,1463,180,398,1076,309,1048,481,1766,-732
    };
    static const int weightsec[40] = {
        179,203,185,136,436,147,289,-1033,343,440,
        313,401,248,189,545,183,288,220,1506,813,
        293,671,240,152,845,151,498,322,1027,312,
        448,1155,361,135,1290,136,941,613,1123,1050
    };

	if (now == Color::Black)
	{//first (black) player
		{//Me, first (black) player
			sum += __builtin_popcountll(rMe & mask_2) * weightfir[((turn - 4) / 14)*10 + 0];//2nd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_3) * weightfir[((turn - 4) / 14)*10 + 1];//3rd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_4) * weightfir[((turn - 4) / 14)*10 + 2];//4th layer_intersection_fir
		}
		{//You, second (white) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightfir[((turn - 4) / 14)*10 + 3];//2nd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_3) * weightfir[((turn - 4) / 14)*10 + 4];//3rd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_4) * weightfir[((turn - 4) / 14)*10 + 5];//4th layer_intersection_fir
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			//assert(intersection < 5);
			//if (__builtin_parityll(intersection_3))
			if(intersection == 1)
			{//odd, black = Me
				sum += weightfir[((turn - 4) / 14)*10 + 6];
			}
			else if(intersection == 2)
			{//even, white = You
				sum -= weightfir[((turn - 4) / 14)*10 + 7];
			}
			else if(intersection == 3)
			sum += weightfir[((turn - 4) / 14)*10 + 8];
			else if(intersection == 4)
			sum -= weightfir[((turn - 4) / 14)*10 + 9];
		}
	}
	else
	{//second (white) player
		{//Me, second (white) player
			sum += __builtin_popcountll(rMe & mask_2) * weightsec[((turn - 5) / 14)*10 + 0];//2nd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_3) * weightsec[((turn - 5) / 14)*10 + 1];//3rd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_4) * weightsec[((turn - 5) / 14)*10 + 2];//4th layer_intersection_sec
		}
		{//You, first (black) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightsec[((turn - 5) / 14)*10 + 3];//2nd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_3) * weightsec[((turn - 5) / 14)*10 + 4];//3rd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_4) * weightsec[((turn - 5) / 14)*10 + 5];//4th layer_intersection_sec
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if (intersection == 1)
			{//odd, black = You
				sum -= weightsec[((turn - 5) / 14)*10 + 6];
			}
			else if(intersection == 2)
			{//even, white = Me
				sum += weightsec[((turn - 5) / 14)*10 + 7];
			}
			else if(intersection == 3)
			sum -= weightsec[((turn - 5) / 14)*10 + 8];
			else if(intersection == 4)
			sum += weightsec[((turn - 5) / 14)*10 + 9];
		}
	}
	return sum;
}

inline int evaluate_pointfir_cont_layer_intersection(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointfir(board, rMe, rYou) + continuous_fir(board, rMe, rYou) - continuous_fir(board, rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
}

inline int evaluate_pointsec_cont_layer_intersection(const Board &board)
{
	const enum Color now = board.player();
	const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
	const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
	const unsigned long long hand = board.valid_move();
	return evaluate_pointsec(board, rMe, rYou) + continuous_sec(board, rMe, rYou) - continuous_sec(board, rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
}
