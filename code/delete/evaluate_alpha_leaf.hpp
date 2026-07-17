#pragma once
#include "evaluate_alpha.hpp"

// 提案2: evaluate_board で計算済みの reach 生値を受け取るラッパー。
// 既存 evaluate_pointfir_cont_layer_intersection (evaluate_alpha.hpp:339) との差は
// 「Board::reach を再計算せず、引数の生値にマスクをかけるだけ」の一点のみ。値は完全一致する。
inline int evaluate_pointfir_cont_layer_intersection_r(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const enum Color now = board.player();
	const unsigned long long rMe  = rMe_raw  & ~board.You;   // マスクのみ。reach 再計算が消える
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointfir(board, rMe, rYou)
	     + continuous_fir(board, rMe, rYou) - continuous_fir(board, rYou, rMe)
	     + reach_layer_intersection(board, now, rMe, rYou, hand);
}

inline int evaluate_pointsec_cont_layer_intersection_r(
	const Board &board, unsigned long long rMe_raw, unsigned long long rYou_raw, unsigned long long hand)
{
	const enum Color now = board.player();
	const unsigned long long rMe  = rMe_raw  & ~board.You;
	const unsigned long long rYou = rYou_raw & ~board.Me;
	return evaluate_pointsec(board, rMe, rYou)
	     + continuous_sec(board, rMe, rYou) - continuous_sec(board, rYou, rMe)
	     + reach_layer_intersection(board, now, rMe, rYou, hand);
}
