// =============================================================================
//  evaluate.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  最初の世代の評価関数(main.cpp が使う)。
//  局面を、決勝点・準Tポイント・Tポイント・重複Tポイントの数で点数にする。
//  後継の evaluate_alpha.hpp は、この関数の重みと特徴を見直したものである。
//
//  用語(本文tex に従う):
//    決勝点       … そこに置けば 4つ並ぶマス(Board::reach() の返すマス)
//    Tポイント    … 3段目の浮き決勝点(直下が空)
//    準Tポイント  … そこに置けば Tポイントができるマス
//    重複Tポイント … 白と黒の Tポイントが重なったマス
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once

#include "common.hpp"
#include "board.hpp"

// -----------------------------------------------------------------------------
// evaluate_pointfir(board, rMe, rYou): 先手(白)の AI 用の「ラインと準Tポイント」の項。
//   rMe / rYou は手番側 / 相手の決勝点(相手の石が無いマスに限る)。値は手番側(Me)から見た点数。
//   turn >= 60(残り 5マス以下)では 0 を返す(終盤は reach_layer_intersection が判定する)。
//   手数は turn_bucket = (turn - 4) / 14 で 4区間に分け、区間ごとに別の重みを使う。
//   1) 各勝ちラインの石数 count[i](-3..3。Me だけなら +、You だけなら -、両方あれば 0)ごとの重み stdweight。
//   2) 自分の石が 2つで残り 2マスが空いているラインについて、空きマスの一方 h が
//      3段目で直下が空(= 自分がもう一方を埋めれば h が Tポイントになる)なら、
//      もう一方のマス make は準Tポイントである。準Tポイントを段ごとに数えて重みを掛ける。
// -----------------------------------------------------------------------------
inline int evaluate_pointfir(const Board &board, unsigned long long rMe, unsigned long long rYou)
{
	const int turn = board.turn();// turn number (the number of stones = turn - 1)
	if(turn >= 60){
		return 0;
	}

	int sum = 0;
	// ラインの石数(-3..3)ごとの重み。7個 × 4区間。
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

	// 準Tポイントの重み。区間ごとに 8個(自分の 1..4段目、相手の 1..4段目)。
	static const int maketweight[32] = {
		-38,-32,52,2,48,-45,32,15,
		158,-54,85,19,80,-45,38,11,
		422,1,143,76,119,10,50,46,
		1009,-90,184,82,165,-26,23,111
	};

	// 直下に石がある準Tポイントの重み。区間ごとに 6個(自分の 2..4段目、相手の 2..4段目)。
	static const int float_maketweight[24] = {
		252,241,72,17,42,22,
		10,294,161,-54,62,47,
		81,488,239,6,109,12,
		105,1002,594,87,113,-39
	};

	for(int i = 0; i < LINES_NUM; i++)
	{
		// 自分の石が 2つ、相手の石が 0 のライン。two はその中の空きマス(2マス)。
		// floatthree: two のうち、3段目にあり、直下のマスが空で、直下が相手の決勝点でもないマス(Tポイントの候補)。
		// << SIZE * SIZE は 1段上へのシフトなので、(X << 16) は「直下が X のマス」の集合になる。
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
				// h: floatthree の最下位ビット(1マス)。make: two のうち h でない方のマス = 準Tポイント。
				// nonfloat_make = make & ~(直下に石があるマス)、float_make = その残り(直下に石があり、すぐに置けるマス)。
				//   ※名前は「浮いていない / 浮いている」だが、式の上では nonfloat_make が直下の空いたマス(と 1段目)、
				//     float_make が直下の埋まったマスになっている。元のコードのまま残している。
				// ~(rYou >> SIZE*SIZE): 直上が相手の決勝点であるマスは除く(そこに置くと、相手にその上を取られて負ける)。
				// mask_1..mask_4 はそれぞれ 1..4段目の 16マス。
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//準Tポイント
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてない準Tポイント
				unsigned long long float_make = make & ~nonfloat_make;//浮いている準Tポイント
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
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてない準Tポイント
				unsigned long long float_make = make & ~nonfloat_make;//浮いている準Tポイント
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
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、Tポイントの候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//準Tポイント
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてない準Tポイント
				unsigned long long float_make = make & ~nonfloat_make;//浮いている準Tポイント
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
				unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてない準Tポイント
				unsigned long long float_make = make & ~nonfloat_make;//浮いている準Tポイント
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

// 常に 0 を返す評価関数(どの手も同点になるので、ランダムな AI になる)。
inline int evaluate_random(const Board &board)
{
	return 0;
}

// -----------------------------------------------------------------------------
// continuous_fir / continuous_sec: 同じ柱で縦に連続する 2つの決勝点(上下の 2マスがどちらも自分の決勝点)の数に、
// 手数の区間ごとの重みを掛ける。直下が相手の決勝点であるマスは先に除く。fir が先手用、sec が後手用。
// -----------------------------------------------------------------------------
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

// -----------------------------------------------------------------------------
// reach_layer_intersection: 決勝点が何段目にあるか、および重複Tポイントの数による項。
//   - 直下が相手の決勝点である自分の決勝点は除く(相手が先に下を取って勝つので、使えない)。
//   - intersection_3: 3段目で、両者の決勝点が重なるマス = 重複Tポイント。これは rMe / rYou から外して別に数える。
//   - turn >= 60(終盤): 本文tex の形勢判断と同じ考え方で、勝ち負けを決め打ちする。
//       白(先手)の手番: 自分の 3段目の決勝点(Tポイント)か重複Tポイントがあれば勝ち、
//                       なければ相手(黒)に 2段目か 4段目の決勝点があれば負け。
//       黒(後手)の手番: 自分に 4段目の決勝点があれば勝ち、
//                       相手(白)に 3段目の決勝点か重複Tポイントがあれば負け。
//     勝ち・負けは ±(INF - 100000) で表す(探索で読み切った勝ち ±INF とは区別する)。
//   - turn < 60: 2・3・4段目の決勝点の数と、重複Tポイントの数(1..4)に、手数の区間ごとの重みを掛ける。
//     重複Tポイントが奇数個なら白に、偶数個なら黒に有利(本文tex: 1つ目は白、2つ目は黒に味方する)。
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
// 評価関数の本体。手番側(Me)から見た評価値を返す。探索(ai_player.hpp)が葉の局面で呼ぶ。
//   rMe / rYou: 手番側 / 相手の決勝点のうち、相手の石が無いマス。
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
