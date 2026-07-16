#pragma once

#include "evaluate_alpha_t.hpp"   // continuous_{fir,sec}_t / reach_layer_intersection_t を流用
#include "board_inc.hpp"          // BoardInc

// 提案7a+7b+7c 統合: BoardInc の増分 cnt[] を添字に、7b 型の単一テーブルを引く評価関数一式(_it / _rit)。
// 7c(evaluate_alpha_inc.hpp)を母体とし、葉の走査ループの 2 段参照
//   v = cnt_to_v[cnt[i]] → stdweight[bucket*7+v+3] → v==±2 判定
// を、cnt バイトを直接添字にした単一テーブル参照へ畳み込む(7b のテーブル畳込み)。
// pext は増分維持により不要(BMI2 非依存)。makeT 検出・重み・tMe/tYou 集約は 7a/7b/7c と同一。
// continuous / reach_layer_intersection は Board(board.b)を渡して _t 版を流用する。
// 評価値は 7a/7b/7c と完全一致する。

// idx = (count_me << 4 | count_you)。cnt バイトをそのまま添字にする(pext 不要)。
alignas(64) inline int stdweight_fir_tbl[4][256];   // [turn_bucket][cnt] → evaluate_pointfir の stdweight 寄与
alignas(64) inline int stdweight_sec_tbl[4][256];   // [turn_bucket][cnt] → evaluate_pointsec の weight 寄与
alignas(64) inline unsigned char flag_tbl[256];     // bit0: v==+2(Me のみ2石), bit1: v==-2(You のみ2石)

inline void init_cnt_tbl()
{
	// 値は evaluate_alpha_pext.hpp / evaluate_alpha_inc.hpp と同一
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
		const int cme = idx >> 4, cyou = idx & 15;                 // ★7b との差分: popcount せず、そのまま石数
		const int v = (cme && cyou) ? 0 : (cme ? cme : -cyou);     // board.count() と同じ規約(両者混在は 0)
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

inline int evaluate_pointfir_it(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
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
	// ★統合: 増分維持済み cnt[] を直接添字に、stdweight 寄与と ±2 判定を単一テーブル参照へ畳み込む
	for(int i = 0; i < LINES_NUM; i++)
	{
		const unsigned b = board.cnt[i];                 // 増分維持済み(pext も count() も不要)
		sum += stdweight_fir_tbl[turn_bucket][b];        // 単一参照(cnt_to_v と bucket*7+v+3 を融合)
		if(flag_tbl[b] & 1)
		{//v == +2: makeT 検出 Me 側(中身は 7a/7b/7c と同一。two は分岐内で計算)
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
		else if(flag_tbl[b] & 2)
		{//v == -2: makeT 検出 You 側
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

inline int evaluate_pointsec_it(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, const int turn, const int turn_bucket)
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
		const unsigned b = board.cnt[i];                 // 増分維持済み(pext も count() も不要)
		sum += stdweight_sec_tbl[turn_bucket][b];        // 単一参照
		if(flag_tbl[b] & 1)
		{//v == +2
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
		else if(flag_tbl[b] & 2)
		{//v == -2
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

// エントリ(_rit)。7c の _ri と同一構造で、evaluate_point の呼び出しだけ _it 版に差し替える。
// signature int(*)(const BoardInc&, ull, ull, ull) は _ri と同一 → ai_player_pvs_inc.hpp を無変更で流用できる。
inline int evaluate_pointfir_cont_layer_intersection_rit(
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
	return evaluate_pointfir_it(board, rMe, rYou, turn, bucket_fir)
	     + continuous_fir_t(board.b, rMe, rYou, turn, bucket_fir)
	     - continuous_fir_t(board.b, rYou, rMe, turn, bucket_fir)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}

inline int evaluate_pointsec_cont_layer_intersection_rit(
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
	return evaluate_pointsec_it(board, rMe, rYou, turn, bucket_sec)
	     + continuous_sec_t(board.b, rMe, rYou, turn, bucket_sec)
	     - continuous_sec_t(board.b, rYou, rMe, turn, bucket_sec)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec);
}
