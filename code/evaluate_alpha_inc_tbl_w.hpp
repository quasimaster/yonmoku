#pragma once

#include "evaluate_alpha_t_w.hpp"   // continuous_{fir,sec}_t / reach_layer_intersection_t の _w 版
#include "board_inc.hpp"            // BoardInc
#include "eval_weights.hpp"         // EvalWeights / flag_tbl

// evaluate_alpha_inc_tbl.hpp の「重み外部ファイル化」版(_w)。
// 設計: docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md §2.2 / §2.3
//
// 流用元 evaluate_alpha_inc_tbl.hpp との差分は次の 3 点だけで、
// 76 ライン走査ループの構造・分岐・添字計算・演算順序は 1 箇所も変えていない。
//   1. static const な重み配列を削除し、末尾引数で渡された EvalWeights を参照する
//        stdweight_fir_tbl[bucket][b]     → W.stdweight_fir_tbl[bucket][b]
//        maketweight[bucket*8 + k]        → W.fir.maketweight[bucket*8 + k]
//        conti_maketweight[bucket*6 + k]  → W.fir.conti_maketweight[bucket*6 + k]
//   2. バケット先頭ポインタをループ外へ巻き上げる(設計書 §4)
//   3. init_cnt_tbl() は EvalWeights::build_tables() + init_flag_tbl() に分解済み
//      (eval_weights.hpp。flag_tbl は重みに依存しないのでグローバルのまま)
// したがって組み込み既定値 EvalWeights::builtin() を渡す限り、
// 返す評価値は evaluate_alpha_inc_tbl.hpp と完全に一致する。

// 流用元 init_cnt_tbl() の置き換え。重みに依存する表はモデル側 (build_tables) が持つ。
inline void init_eval_tbl()
{
	init_flag_tbl();
}

inline int evaluate_pointfir_it(const BoardInc &board, unsigned long long rMe, unsigned long long rYou,
                                const int turn, const int turn_bucket, const EvalWeights &W)
{
	if(turn >= 60){
		return 0;
	}

	int sum = 0;

	// ★巻き上げ(現行 maketweight[turn_bucket*8 + k] / conti_maketweight[turn_bucket*6 + k] と同一)
	const int* const sw = W.stdweight_fir_tbl[turn_bucket];
	const int* const mw = W.fir.maketweight       + turn_bucket * 8;
	const int* const cw = W.fir.conti_maketweight + turn_bucket * 6;

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
		sum += sw[b];                                    // 単一参照(cnt_to_v と bucket*7+v+3 を融合)
		if(flag_tbl[b] & 1)
		{//v == +2: makeT 検出 Me 側(中身は 7a/7b/7c と同一。two は分岐内で計算)
			unsigned long long two = ~board.b.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.b.Me | board.b.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//makeT点
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * mw[0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * mw[1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * mw[2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * mw[3];
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
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * mw[4];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * mw[5];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * mw[6];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * mw[7];
				floatthree ^= h;
			}
		}
	}
	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * cw[0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * cw[1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * cw[2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * cw[3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * cw[4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * cw[5];
    return sum;
}

inline int evaluate_pointsec_it(const BoardInc &board, unsigned long long rMe, unsigned long long rYou,
                                const int turn, const int turn_bucket, const EvalWeights &W)
{
	if(turn >= 60){
		return 0;
	}
	int sum = 0;

	const int* const sw = W.stdweight_sec_tbl[turn_bucket];
	const int* const mw = W.sec.maketweight       + turn_bucket * 8;
	const int* const cw = W.sec.conti_maketweight + turn_bucket * 6;

	static const unsigned long long mask_1 = 0x000000000000ffffuLL;
	static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
	static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
	static const unsigned long long mask_4 = 0xffff000000000000uLL;
    unsigned long long tMe = 0uLL;
    unsigned long long tYou = 0uLL;
	for(int i = 0; i < LINES_NUM; i++)
	{
		const unsigned b = board.cnt[i];                 // 増分維持済み(pext も count() も不要)
		sum += sw[b];                                    // 単一参照
		if(flag_tbl[b] & 1)
		{//v == +2
			unsigned long long two = ~board.b.Me & LINES[i];//LINE内の玉が入っていない部分
			unsigned long long floatthree = two & mask_3 & ~((rYou | board.b.Me | board.b.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
			while(floatthree)
			{
				unsigned long long h = floatthree & -floatthree;
				unsigned long long make = two & ~h;//makeT点
                tMe |= make;
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * mw[0];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * mw[1];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * mw[2];
				sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * mw[3];
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
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * mw[4];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * mw[5];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * mw[6];
				sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * mw[7];
				floatthree ^= h;
			}
		}
	}
	sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * cw[0];//T_T
	sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * cw[1];//T_W
	sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * cw[2];//W_T

	sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * cw[3];
	sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * cw[4];
	sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * cw[5];
    return sum;
}

// エントリ(_rit)。流用元と同一構造で、末尾に EvalWeights を足しただけ。
inline int evaluate_pointfir_cont_layer_intersection_rit(
	const BoardInc &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand,
	const EvalWeights &W)
{
	assert(board_inc_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_pointfir_it(board, rMe, rYou, turn, bucket_fir, W)
	     + continuous_fir_t(board.b, rMe, rYou, turn, bucket_fir, W.fir)
	     - continuous_fir_t(board.b, rYou, rMe, turn, bucket_fir, W.fir)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec, W);
}

inline int evaluate_pointsec_cont_layer_intersection_rit(
	const BoardInc &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand,
	const EvalWeights &W)
{
	assert(board_inc_consistent(board));
	const int turn = board.b.turn();
	const int bucket_fir = (turn - 4) / 14;
	const int bucket_sec = (turn - 5) / 14;
	const enum Color now = (turn - 1) & 1 ? Color::White : Color::Black;
	assert(now == board.b.player());
	const unsigned long long rMe  = rMe_raw  & ~board.b.You;
	const unsigned long long rYou = rYou_raw & ~board.b.Me;
	return evaluate_pointsec_it(board, rMe, rYou, turn, bucket_sec, W)
	     + continuous_sec_t(board.b, rMe, rYou, turn, bucket_sec, W.sec)
	     - continuous_sec_t(board.b, rYou, rMe, turn, bucket_sec, W.sec)
	     + reach_layer_intersection_t(board.b, now, rMe, rYou, hand, turn, bucket_fir, bucket_sec, W);
}

// ===== ファンクタ(設計書 §2.3)=====
// AIPlayerPVSIncID<F> は F をメンバに持ち evaluate_func(board, rMe, rYou, hand) と呼ぶだけなので、
// これをテンプレート引数に渡せば ai_player_pvs_inc_id.hpp を無変更のまま
// プレイヤーごとに別モデルを使わせられる。
struct EvalFn
{
	const EvalWeights* w;
	bool sec;    // false = 先手用エントリ / true = 後手用エントリ

	int operator()(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, unsigned long long hand) const
	{
		return sec ? evaluate_pointsec_cont_layer_intersection_rit(board, rMe, rYou, hand, *w)
		           : evaluate_pointfir_cont_layer_intersection_rit(board, rMe, rYou, hand, *w);
	}
};
