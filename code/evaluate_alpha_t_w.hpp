// =============================================================================
//  evaluate_alpha_t_w.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  evaluate_alpha_t.hpp の重みを外部ファイルから読めるようにした版(_w)。
//  重みは関数の最後の引数で受け取る(SideWeights は片方の手番用、EvalWeights は先手用と後手用の両方)。
//  組み込みの既定値 EvalWeights::builtin() を渡せば、evaluate_alpha_t.hpp と同じ評価値を返す。
//  rB / rW は、色の入れ替えに合わせて rW(白の決勝点)/ rB(黒の決勝点)と名前を入れ替えた。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once

#include "common.hpp"
#include "board.hpp"
#include "eval_weights.hpp"

// evaluate_alpha_t.hpp の「重み外部ファイル化」版(_w)。
// 設計: docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md §2.2
//
// 流用元 evaluate_alpha_t.hpp との差分は次の 2点だけで、
// ループ構造・分岐・添字計算・演算順序は 1 箇所も変えていない。
//   1. static const な重み配列を削除し、末尾引数で渡された重みを参照する
//        parameter[bucket]           → S.continuous[bucket]
//        weightfir[bucket_fir*10+k]  → W.fir.layer_inter[bucket_fir*10+k]
//        weightsec[bucket_sec*10+k]  → W.sec.layer_inter[bucket_sec*10+k]
//   2. バケット先頭ポインタをループ外へ巻き上げる(設計書 §4)
// したがって組み込み既定値 EvalWeights::builtin() を渡す限り、
// 返す評価値は evaluate_alpha_t.hpp と完全に一致する。
//
// 注意: reach_layer_intersection_t は手番 now に応じて fir/sec を両方参照するため、
// 受け取るのは片側 SideWeights ではなくモデル全体 EvalWeights でなければならない。

// フェーズ1(最終盤の葉評価を規則 R0 → R2 に差し替え)。
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md §3.4
//   0 = 現行の R0(既存ビルドの挙動は完全に不変)
//   1 = 段パリティ定理 + 低段優先の R2(turn=60 で誤断定 4.1% → 1.8%)
#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 0
#endif

// 縦に連続する 2つの決勝点の項。重みは S.continuous[区間]。
// _fir が先手(白)用、_sec が後手(黒)用(計算は同じで、渡す重みと区間が違う)。
inline int continuous_fir_t(const Board &board, unsigned long long rMe, const unsigned long long rYou,
                            const int turn, const int turn_bucket, const SideWeights &S)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * S.continuous[turn_bucket];
}

inline int continuous_sec_t(const Board &board, unsigned long long rMe, const unsigned long long rYou,
                            const int turn, const int turn_bucket, const SideWeights &S)
{
	if(turn >= 60){
		return 0;
	}
	rMe &= ~(rYou << SIZE * SIZE);
	return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * S.continuous[turn_bucket];
}

// 決勝点の段と重複Tポイントの数の項。重みは W.fir.layer_inter / W.sec.layer_inter(区間ごとに 10個)。
// 手番 now によって先手用と後手用のどちらの重みも使うので、両方を持つ EvalWeights を受け取る。
inline int reach_layer_intersection_t(const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand,
                                      const int turn, const int bucket_fir, const int bucket_sec, const EvalWeights &W)
{
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
#if USE_ENDGAME_R2
		// 規則 R2: 段パリティ定理(白 = 奇数段 / 黒 = 偶数段)+ 低段優先(低い段の脅威が先に発火)。
		// rMe/rYou はエスケープフィルタ適用後。intersection_3 は3段目 = 奇数段なので白側に数える。
		// 判定順 mask_2 → mask_3 → mask_4 が本質(順序を崩すと R0 の欠陥B が再発する)。
		{
			// rW / rB: 白 / 黒の決勝点(手番に関係なく色で持ち直す)。
			const unsigned long long rW = (now == Color::White) ? rMe  : rYou;
			const unsigned long long rB = (now == Color::White) ? rYou : rMe;
			int v = 0;                                             // +1 = 白勝ち / -1 = 黒勝ち
			if      (rB & mask_2)                     v = -1;      // 黒の2段目(R0 の欠陥A: 黒番分岐に無かった)
			else if ((rW & mask_3) || intersection_3) v = +1;      // 白の3段目
			else if (rB & mask_4)                     v = -1;      // 黒の4段目(R0 の欠陥B: 白の3段目より先に見ていた)
			if (v) sum = ((now == Color::White) ? v : -v) * (INF - 100000);
		}
// 規則 R0(既定): evaluate_alpha.hpp と同じ判定(白は Tポイントか重複Tポイント、黒は 4段目の決勝点で勝ち)。
#else
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
#endif
		return sum;
	}

	if (now == Color::White)
	{//first (white) player
		const int* const wf = W.fir.layer_inter + bucket_fir * 10;   // ★巻き上げ(現行 weightfir[bucket_fir*10 + k] と同一)
		{//Me, first (white) player
			sum += __builtin_popcountll(rMe & mask_2) * wf[0];//2nd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_3) * wf[1];//3rd layer_intersection_fir
			sum += __builtin_popcountll(rMe & mask_4) * wf[2];//4th layer_intersection_fir
		}
		{//You, second (black) player
			sum -= __builtin_popcountll(rYou & mask_2) * wf[3];//2nd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_3) * wf[4];//3rd layer_intersection_fir
			sum -= __builtin_popcountll(rYou & mask_4) * wf[5];//4th layer_intersection_fir
		}
		// 重複Tポイントの数による項。奇数個なら白に、偶数個なら黒に有利。
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if(intersection == 1)
			{//odd, white = Me
				sum += wf[6];
			}
			else if(intersection == 2)
			{//even, black = You
				sum -= wf[7];
			}
			else if(intersection == 3)
			sum += wf[8];
			else if(intersection == 4)
			sum -= wf[9];
		}
	}
	else
	{//second (black) player
		const int* const ws = W.sec.layer_inter + bucket_sec * 10;   // ★巻き上げ(現行 weightsec[bucket_sec*10 + k] と同一)
		{//Me, second (black) player
			sum += __builtin_popcountll(rMe & mask_2) * ws[0];//2nd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_3) * ws[1];//3rd layer_intersection_sec
			sum += __builtin_popcountll(rMe & mask_4) * ws[2];//4th layer_intersection_sec
		}
		{//You, first (white) player
			sum -= __builtin_popcountll(rYou & mask_2) * ws[3];//2nd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_3) * ws[4];//3rd layer_intersection_sec
			sum -= __builtin_popcountll(rYou & mask_4) * ws[5];//4th layer_intersection_sec
		}
		if (intersection_3)
		{//if there exists intersections of reaches on 3rd layer
			int intersection = __builtin_popcountll(intersection_3);
			if (intersection == 1)
			{//odd, white = You
				sum -= ws[6];
			}
			else if(intersection == 2)
			{//even, black = Me
				sum += ws[7];
			}
			else if(intersection == 3)
			sum -= ws[8];
			else if(intersection == 4)
			sum += ws[9];
		}
	}
	return sum;
}
