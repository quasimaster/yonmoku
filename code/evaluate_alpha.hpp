// =============================================================================
//  evaluate_alpha.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  evaluate.hpp を改良した評価関数(alpha 版)。main_alpha.cpp が使う。
//  後の世代(evaluate_alpha_t.hpp、evaluate_alpha_inc_tbl*.hpp)は、どれもこの関数と同じ特徴を同じ式で、より速く計算する版である(重みの値は版ごとに違う)。
//
//  evaluate.hpp との違い:
//    - 重みを学び直した。
//    - 準Tポイントを「直下が空かどうか」で分けず、1種類として段ごとに数える。
//    - 準Tポイントの集合 tMe / tYou を作り、同じ柱で縦に重なる組を数える項(conti_maketweight)を足した。
//        T_T … 準Tポイントの真上が準Tポイント
//        T_W … 準Tポイントの真上が決勝点
//        W_T … 決勝点の真上が準Tポイント
//
//  用語(本文tex に従う): 決勝点、Tポイント(3段目の浮き決勝点)、準Tポイント、重複Tポイント。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once

#include "common.hpp"
#include "board.hpp"

// -----------------------------------------------------------------------------
// evaluate_pointfir(board, rMe, rYou): 先手(白)の AI 用の「ラインと準Tポイント」の項。値は手番側(Me)から見た点数。
//   計算の流れは evaluate.hpp の同名関数と同じ(そちらのコメントを参照)。turn >= 60 では 0 を返す。
// -----------------------------------------------------------------------------
inline int evaluate_pointfir(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}

	int sum = 0;
	// ラインの石数(-3..3)ごとの重み。7個 × 4区間。
	// ※最後の区間は初期値が 6個しか書かれていないので、残りの 1個(石数 +3 の重み)は 0 になる。
	static const int stdweight[28] = {
		0,-58,-20,0,27,57,0,
		0,-58,-20,0,27,57,0,
		0,-86,-9,0,22,56,0,
		0,-96,-31,-10,29,0
	};
	auto count = board.count();
	const int turn_bucket = (turn - 4) / 14;
	for (int v : count){
		assert(v >= -3 && v <= 3);
		sum += stdweight[turn_bucket * 7 + v + 3];//0~4,5~14,...,45~54
	}

	// 準Tポイントの重み。区間ごとに 8個(自分の 1..4段目、相手の 1..4段目)。
	static const int maketweight[32] = {
		-80,-38,45,0,5,-33,26,14,
		117,-62,68,27,52,-58,38,14,
		179,-53,120,78,109,-18,44,30,
		287,-176,139,100,248,-17,48,20
	};

	// 縦に重なる準Tポイントの重み。区間ごとに 6個(自分の T_T、T_W、W_T、相手の T_T、T_W、W_T)。
	static const int conti_maketweight[24] = {
		109,143,384,66,119,174,
		203,252,52,80,101,64,
		362,648,100,135,294,28,
		689,1192,84,304,518,-169
	};

    // tMe / tYou: 見つけた準Tポイントの集合(縦の重なりを最後に数えるために集める)。
    unsigned long long tMe = 0uLL;
    unsigned long long tYou = 0uLL;
	for(int i = 0; i < LINES_NUM; i++)
	{
		// 自分の石が 2つ、相手の石が 0 のライン。two はその中の空きマス(2マス)。
		// floatthree: two のうち、3段目にあり、直下が空で、直下が相手の決勝点でもないマス(Tポイントの候補)。
		if(count[i] == 2)
		{
			unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
			static const unsigned long long mask_1 = 0x000000000000ffffuLL;
			static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
			static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
			static const unsigned long long mask_4 = 0xffff000000000000uLL;
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、Tポイントの候補
			while(floatthree)
			{
				// h: Tポイントの候補 1マス。make: two のうち h でない方 = 準Tポイント。
				// 直上が相手の決勝点である準Tポイントは数えない(~(rYou >> SIZE*SIZE))。
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//準Tポイント
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
				floatthree ^= h;
			}
		}
		// 相手の石が 2つのライン。上と同じ計算を相手について行い、引き算する。
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

				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
				floatthree ^= h;
			}

		}

	}
	// 縦に重なる準Tポイントの項。(X << SIZE * SIZE) は「直下が X のマス」なので、
	// A & (B << 16) は「直下が B で、そのマス自身が A」のマスの集合になる。
	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 5];
    return sum;

}

// -----------------------------------------------------------------------------
// evaluate_pointsec(board, rMe, rYou): 後手(黒)の AI 用の同じ項。
//   処理は evaluate_pointfir と同じで、重みと手数の区間 turn_bucket = (turn - 5) / 14 だけが違う。
// -----------------------------------------------------------------------------
inline int evaluate_pointsec(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
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
	const int turn_bucket = (turn - 5) / 14;
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
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、Tポイントの候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//準Tポイント
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
				// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
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

				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
				// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
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

// 常に 0 を返す評価関数(どの手も同点になるので、ランダムな AI になる)。
inline int evaluate_random(const Board &board)
{
	return 0;
}

// -----------------------------------------------------------------------------
// continuous_fir / continuous_sec: 同じ柱で縦に連続する 2つの決勝点の数に、手数の区間ごとの重みを掛ける。
// 直下が相手の決勝点であるマスは先に除く。fir が先手(白)用、sec が後手(黒)用。
// -----------------------------------------------------------------------------
inline int continuous_fir(const Board &board, unsigned long long rMe, const unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	static const int parameter[4] = {860,1034,649,527};
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
	static const int parameter[4] = {1158,1037,707,657};
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[(turn - 5) / 14];
}

// -----------------------------------------------------------------------------
// reach_layer_intersection: 決勝点の段と重複Tポイントの数による項。evaluate.hpp と同じ処理で、重みだけが違う。
//   - 直下が相手の決勝点である決勝点は除く。3段目で両者の決勝点が重なるマス(重複Tポイント)は別に数える。
//   - turn >= 60: 白(先手)は Tポイントか重複Tポイントがあれば勝ち、黒(後手)は 4段目の決勝点があれば勝ち、
//     と決め打ちする(±(INF - 100000))。
//   - turn < 60: 2・3・4段目の決勝点の数と、重複Tポイントの数(1..4)に重みを掛ける。
// -----------------------------------------------------------------------------
inline int reach_layer_intersection(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)

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

	if (now == Color::White)
	{//first (white) player
		{//Me, first (white) player
			sum += __builtin_popcountll(rMe & mask_2) * weightfir[((turn - 4) / 14)*10 + 0];//2nd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_3) * weightfir[((turn - 4) / 14)*10 + 1];//3rd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_4) * weightfir[((turn - 4) / 14)*10 + 2];//4th layer_intersection_fir
		}
		{//You, second (black) player
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
			{//odd, white = Me
				sum += weightfir[((turn - 4) / 14)*10 + 6];
			}
			else if(intersection == 2)
			{//even, black = You
				sum -= weightfir[((turn - 4) / 14)*10 + 7];
			}
			else if(intersection == 3)
			sum += weightfir[((turn - 4) / 14)*10 + 8];
			else if(intersection == 4)
			sum -= weightfir[((turn - 4) / 14)*10 + 9];
		}
	}
	else
	{//second (black) player
		{//Me, second (black) player
			sum += __builtin_popcountll(rMe & mask_2) * weightsec[((turn - 5) / 14)*10 + 0];//2nd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_3) * weightsec[((turn - 5) / 14)*10 + 1];//3rd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_4) * weightsec[((turn - 5) / 14)*10 + 2];//4th layer_intersection_sec
		}
		{//You, first (white) player
			sum -= __builtin_popcountll(rYou & mask_2) * weightsec[((turn - 5) / 14)*10 + 3];//2nd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_3) * weightsec[((turn - 5) / 14)*10 + 4];//3rd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_4) * weightsec[((turn - 5) / 14)*10 + 5];//4th layer_intersection_sec
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if (intersection == 1)
			{//odd, white = You
				sum -= weightsec[((turn - 5) / 14)*10 + 6];
			}
			else if(intersection == 2)
			{//even, black = Me
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

// -----------------------------------------------------------------------------
// 評価関数の本体。手番側(Me)から見た評価値を返す。
//   合計 = 準Tポイントの項 + 自分の縦の連続決勝点 - 相手の縦の連続決勝点 + 段と重複Tポイントの項
// _fir が先手(白)の AI 用、_sec が後手(黒)の AI 用。
// -----------------------------------------------------------------------------
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
