#pragma once

#include "common.hpp"
#include "board.hpp"

// 提案7a: turn の集約(implementation-plan-eval-speedup.md §3.1)。
// evaluate_alpha.hpp の各関数のコピーに turn / turn_bucket を引数で足し、
// 関数先頭の「const int turn = board.turn();」(popcount)と bucket 計算を削除したもの(_t サフィックス)。
// turn >= 60 の早期 return はサブ関数側に残し、条件分岐の構造は変えない。
// エントリ _rt はシグネチャが evaluate_alpha_leaf.hpp の _r 版と同一で、評価値は完全一致する。

inline int evaluate_pointfir_t(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
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
	auto count = board.count();
	for (int v : count){
		assert(v >= -3 && v <= 3);
		sum += stdweight[turn_bucket * 7 + v + 3];//0~4,5~14,...,45~54
	}

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
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];
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

inline int evaluate_pointsec_t(const Board &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
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

	auto count = board.count();
	for (int v : count){
		assert(v >= -3 && v <= 3);
		sum += weight[turn_bucket * 7 + v + 3];//1~3,4~13,...,44~53
	}
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
		if(count[i] == 2)
		{
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
		else if(count[i] == -2)
		{
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

inline int continuous_fir_t(const Board &board, unsigned long long rMe, const unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {860,1034,649,527};
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[turn_bucket];
}

inline int continuous_sec_t(const Board &board, unsigned long long rMe, const unsigned long long rYou, const int turn, const int turn_bucket)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {1158,1037,707,657};
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
		125,484,129,185,228,181,136,583,1342,1157,
        166,579,149,297,357,224,318,290,565,-1018,
        156,881,89,318,634,238,492,454,1114,-575,
        190,1515,109,448,1001,316,1097,637,1989,1031
    };
    static const int weightsec[40] = {
        230,235,178,141,451,148,307,1356,208,-809,
        310,387,233,174,537,159,271,296,1504,-181,
        292,719,230,151,916,88,543,445,1029,235,
        491,1305,365,157,1434,58,1083,1036,1630,-1088
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

// エントリ(_rt)。turn(popcount)・両バケット・手番をここで1回だけ計算してサブ関数へ渡す。
// (turn - 1) & 1 による手番導出は Board::player() の __builtin_parityll(Me | You) と同値
// (石数 = turn - 1)。assert で同値性を検証する(NDEBUG で消える)。
inline int evaluate_pointfir_cont_layer_intersection_rt(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const int turn = board.turn();                 // ★葉で唯一の popcount 呼び出しに集約
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;  // ★player() の parity も置換
	assert(now == board.player());
	const unsigned long long rMe  = rMe_raw  & ~board.You;
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointfir_t(board, rMe, rYou, turn, bucket_fir)
	     + continuous_fir_t(board, rMe, rYou, turn, bucket_fir)
	     - continuous_fir_t(board, rYou, rMe, turn, bucket_fir)
	     + reach_layer_intersection_t(board, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}

inline int evaluate_pointsec_cont_layer_intersection_rt(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const int turn = board.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.player());
	const unsigned long long rMe  = rMe_raw  & ~board.You;
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointsec_t(board, rMe, rYou, turn, bucket_sec)
	     + continuous_sec_t(board, rMe, rYou, turn, bucket_sec)
	     - continuous_sec_t(board, rYou, rMe, turn, bucket_sec)
	     + reach_layer_intersection_t(board, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}
