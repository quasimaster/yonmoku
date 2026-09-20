#pragma once

#include "evaluate_alpha_inc_tbl_w.hpp"   // 既存の評価関数(重み外部化版)。無変更で使う
#include "eval_weights_core.hpp"          // EvalWeightsCore
#include "core_feature.hpp"               // core_feat::counts

// 既存評価 + 「核 2 マスの全状態」(6 本 / バケット)の評価関数。
// 設計: docs/設計書/評価関数パラメータ/investigation-new-eval-features.md §2.6 D
//
// 評価値 = 既存の evaluate_point{fir,sec}_cont_layer_intersection_rit(base 重み)
//        + Σ_k core_feat::counts()[k] × core[bucket*6 + k]
//
// 既存の評価関数には手を入れず、外側で核の項を足すだけにしてある。
// そのため core を全部 0 にしたモデル(= version 1 の重みファイル / builtin)では、
// EvalFn(evaluate_alpha_inc_tbl_w.hpp)と 1 ノードも変わらない。
//
// 核の項は 76 ライン走査ループの外で、葉 1 回あたり シフト 2・AND/ANDN 8・popcount 6。
// turn >= 60 では加算しない(既存の evaluate_point*_it / continuous_*_t が
// turn >= 60 で 0 を返し、最終盤を段パリティによる判定に任せているのに合わせる。§2.5 注意点 2)。
// バケットは既存と同じ 先手 (turn-4)/14、後手 (turn-5)/14。
// (turn = 60 で先手バケットは 4 になり範囲外なので、turn の判定を必ず先に行う)

inline int core_term(const Board &board, const int* const cw)
{
	int f[core_feat::NUM];
	core_feat::counts(board.Me, board.You, f);
	int sum = 0;
	for (int k = 0; k < core_feat::NUM; k++) sum += f[k] * cw[k];
	return sum;
}

// AIPlayerPVSIncID<F> に渡すファンクタ。EvalFn と同じ呼び出し形で、重みだけ EvalWeightsCore を持つ。
struct EvalFnCore
{
	const EvalWeightsCore* w;
	bool sec;    // false = 先手用エントリ / true = 後手用エントリ

	int operator()(const BoardInc &board, unsigned long long rMe, unsigned long long rYou, unsigned long long hand) const
	{
		int v = sec ? evaluate_pointsec_cont_layer_intersection_rit(board, rMe, rYou, hand, w->base)
		            : evaluate_pointfir_cont_layer_intersection_rit(board, rMe, rYou, hand, w->base);
		const int turn = board.b.turn();
		if (turn < 60)
		{
			const int* const cw = sec ? w->core_sec + ((turn - 5) / 14) * core_feat::NUM
			                          : w->core_fir + ((turn - 4) / 14) * core_feat::NUM;
			v += core_term(board.b, cw);
		}
		return v;
	}
};
