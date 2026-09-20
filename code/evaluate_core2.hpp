#pragma once

#include "evaluate_core.hpp"               // core_term(無変更で流用。流用元の EvalFnCore もここに入るが名前は衝突しない)
#include "evaluate_alpha_inc_tbl_w2.hpp"   // _rit2 / BoardInc2 / EvalWeightsCore2

// evaluate_core.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md)。
// 流用元 EvalFnCore との差分は「BoardInc → BoardInc2、EvalWeightsCore → EvalWeightsCore2、_rit → _rit2」だけで、
// 評価値 = 既存評価 + 核 2 マスの項 は完全に同一。
struct EvalFnCore2
{
	const EvalWeightsCore2* w;
	bool sec;    // false = 先手用エントリ / true = 後手用エントリ

	int operator()(const BoardInc2 &board, unsigned long long rMe, unsigned long long rYou, unsigned long long hand) const
	{
		int v = sec ? evaluate_pointsec_cont_layer_intersection_rit2(board, rMe, rYou, hand, *w)
		            : evaluate_pointfir_cont_layer_intersection_rit2(board, rMe, rYou, hand, *w);
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
