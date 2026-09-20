#pragma once

#include "common.hpp"

// 核(中心 4 棒の z=1, z=2 の 2 マス)の状態を数える特徴量。
// 設計: docs/設計書/評価関数パラメータ/investigation-new-eval-features.md §2.6「D 核 2 マスの全状態」
//
// 探索側(code/evaluate_core.hpp)と学習側(MachineLearning/main_gd_core.cpp)の両方が
// この 1 関数を呼ぶ。定義を 1 か所にして、学習した特徴量と探索が評価する特徴量が
// 食い違わないようにするため。
//
// 中心 4 棒((x,y) = (1,1),(2,1),(1,2),(2,2)。LINES 添字 5,6,9,10)のそれぞれについて、
// 核 2 マスの状態を次の 7 通りに分け、状態 1..6 に当たる棒の本数(各 0..4)を返す。
// 状態 0(z=1 が空 = 核が未充填)は基準として重み 0 に固定する。
// 4 本の出現数の合計が常に 4 になり、1 自由度が識別できないため(同 §3.2)。
//
//          | z=1(下の核) | z=2(上の核) | 調査時の学習値 fir b1(参考)
//   -------+--------------+--------------+------------------------------
//   (基準) | 空           | 空           | 0(学習しない)
//   out[0] | 自           | 空           |  +116
//   out[1] | 敵           | 空           |   +42
//   out[2] | 自           | 自           |  +105   (= 案① 自分の核ペア)
//   out[3] | 自           | 敵           |    +9
//   out[4] | 敵           | 自           |   -37
//   out[5] | 敵           | 敵           |   -89   (= 案① 相手の核ペア)
//
// 「自」= Me = 手番側の石。探索の board.b.Me、学習の Board::place() 後の c.Me と同じ向き。
// 重力があるので z=1 が空なら z=2 も必ず空であり、上の 6 通り + 基準で全状態を尽くす。
//
// ビット配置は IDX(x,y,z) = x + 4y + 16z(common.hpp)。
//   CORE_Z1 = 中心 4 棒の z=1 の 4 マス
//   (B >> 16) & CORE_Z1 で「z=2 のマスを z=1 の位置へ下ろしたもの」になる。

namespace core_feat
{
	inline constexpr int NUM = 6;                                     // 学習するパラメータ本数(1 バケットあたり)
	inline constexpr unsigned long long CORE_Z1 = 0x0000000006600000uLL;

	// 状態名(ログ・重みファイルのコメント用)。out[] と同じ順序。
	inline const char* const NAME[NUM] = {"Me/-", "You/-", "Me/Me", "Me/You", "You/Me", "You/You"};

	inline void counts(const unsigned long long Me, const unsigned long long You, int out[NUM])
	{
		const unsigned long long m1 =  Me              & CORE_Z1;       // z=1 が自分
		const unsigned long long y1 =  You             & CORE_Z1;       // z=1 が相手
		const unsigned long long m2 = (Me  >> SIZE * SIZE) & CORE_Z1;   // z=2 が自分(z=1 の位置へ下ろした)
		const unsigned long long y2 = (You >> SIZE * SIZE) & CORE_Z1;   // z=2 が相手
		const unsigned long long o2 = m2 | y2;
		out[0] = __builtin_popcountll(m1 & ~o2);
		out[1] = __builtin_popcountll(y1 & ~o2);
		out[2] = __builtin_popcountll(m1 & m2);
		out[3] = __builtin_popcountll(m1 & y2);
		out[4] = __builtin_popcountll(y1 & m2);
		out[5] = __builtin_popcountll(y1 & y2);
	}
}
