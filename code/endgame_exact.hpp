#pragma once

#include "common.hpp"
#include "board.hpp"
#include "board_inc.hpp"

// 最終盤の厳密評価(段パリティ規則 R2 + ゲート)。
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md
// 研究: 研究/最終盤評価関数_研究結果.md / 研究/最終盤評価関数_追加検証.md
//
// 本ヘッダは 2 つの部品を提供する。
//   (1) endgame_value()  … 段パリティ定理 + 低段優先による手番視点の勝敗値(規則 R2)
//   (2) endgame_gate()   … 「R2 が厳密であることを証明できる局面」に限定するゲート
// ゲートを通過した局面でのみ (1) は【厳密】であり、level に無関係に部分木を刈ってよい。
// ゲートを通過しない局面については何も断定しない(呼び出し側は通常探索を続ける)。
//
// 【前提】どちらの関数も「制約(C): 即座に置けるマスの上に双方のリーチが無い」の
//         成立する位置でのみ呼ぶこと。探索側では ai_player_pvs_inc_id.hpp の
//         reach ブロック内 `else`(= 即勝ちも阻止強制も無い枝)がその唯一の位置である。

static const unsigned long long EG_MASK_2 = 0x00000000ffff0000uLL;   // 段2 (z=1)
static const unsigned long long EG_MASK_3 = 0x0000ffff00000000uLL;   // 段3 (z=2)
static const unsigned long long EG_MASK_4 = 0xffff000000000000uLL;   // 段4 (z=3)

// 勝ちスコアの絶対値。現行 evaluate_alpha_t.hpp の turn>=60 分岐と同じ規約。
//   即勝ち INF - turn(≈ 999,999,940)より小さい ⇒ 即詰み優先の順序は保たれる
//   負け -(INF - 100000) は即負け -(INF - (turn+1)) より大きい ⇒ 遅い負けが選ばれる
static const int EG_WIN = INF - 100000;

// ---------------------------------------------------------------- 規則 R2

// 手番視点の厳密値(+ = 手番側の勝ち / 0 = 引き分け / - = 手番側の負け)。
// rMe_raw / rYou_raw は Board::reach() の生値(呼び出し側の再計算を避けるため生で受ける)。
inline int endgame_value(const Board &b, const int turn,
                         const unsigned long long rMe_raw, const unsigned long long rYou_raw)
{
	// 評価関数エントリ(evaluate_alpha_inc_tbl.hpp:211-212)と同じ正規化(空きマス上のリーチだけ残す)
	unsigned long long rMe  = rMe_raw  & ~b.You;
	unsigned long long rYou = rYou_raw & ~b.Me;

	// エスケープフィルタ(evaluate_alpha_t.hpp:39-43 と同一。同一柱内の低段優先と等価)
	const unsigned long long rMe_tmp = rMe;
	rMe  &= ~(rYou    << SIZE * SIZE);
	rYou &= ~(rMe_tmp << SIZE * SIZE);

	// 段3 の「両者リーチ」(evaluate_alpha_t.hpp:49-51 と同一)。段3 は奇数段なので黒の脅威。
	const unsigned long long inter3 = (rMe & rYou) & EG_MASK_3;
	rMe  ^= inter3;
	rYou ^= inter3;

	const enum Color now = ((turn - 1) & 1) ? Color::White : Color::Black;   // 7a と同じ導出
	const unsigned long long rB = (now == Color::Black) ? rMe  : rYou;
	const unsigned long long rW = (now == Color::Black) ? rYou : rMe;

	// 段パリティ定理: 黒は奇数段(制約(C) の下で実効は段3)、白は偶数段(段2・段4)。
	// 低段優先: 有効な脅威が複数あるとき最も低い段の保有者が勝つ。判定順序が本質。
	int v = 0;                                       // +1 = 黒勝ち / -1 = 白勝ち
	if      (rW & EG_MASK_2)             v = -1;     // 白の段2
	else if ((rB & EG_MASK_3) || inter3) v = +1;     // 黒の段3
	else if (rW & EG_MASK_4)             v = -1;     // 白の段4
	if (!v) return 0;
	return ((now == Color::Black) ? v : -v) * EG_WIN;
}

// ---------------------------------------------------------------- ゲート

#if defined(__SSE2__) || defined(_M_X64) || defined(_M_AMD64)
  #include <emmintrin.h>
  #define EG_USE_SSE2 1
#else
  #define EG_USE_SSE2 0
#endif

// cnt[i] = (Me 石数 << 4) | You 石数。80 byte(76 本 + 0 初期化パディング 4)。
//   G_A  : 「2石 + 空き2」のラインが無い          = cnt が 0x20 / 0x02 でない
//   G_A2 : G_A に加えて「1石 + 空き3」も無い      = cnt が 0x10 / 0x20 / 0x01 / 0x02 でない
// 判定値集合はどちらもニブル交換に対して対称なので place_fast_clone の Me/You スワップの影響を受けない。
// パディングは 0x00 なのでどちらの集合にも当たらない。

#define EG_HASZERO(v)     (((v) - 0x0101010101010101uLL) & ~(v) & 0x8080808080808080uLL)
#define EG_HASVALUE(x, n) EG_HASZERO((x) ^ (0x0101010101010101uLL * (unsigned long long)(n)))

inline bool eg_gate_A_swar(const unsigned long long *cnt64)
{
	unsigned long long acc = 0uLL;
	for (int i = 0; i < 10; i++)
	{
		const unsigned long long x = cnt64[i];
		acc |= EG_HASVALUE(x, 0x20) | EG_HASVALUE(x, 0x02);
	}
	return acc == 0uLL;
}

inline bool eg_gate_A2_swar(const unsigned long long *cnt64)
{
	unsigned long long acc = 0uLL;
	for (int i = 0; i < 10; i++)
	{
		const unsigned long long x = cnt64[i];
		acc |= EG_HASVALUE(x, 0x20) | EG_HASVALUE(x, 0x02)
		     | EG_HASVALUE(x, 0x10) | EG_HASVALUE(x, 0x01);
	}
	return acc == 0uLL;
}

#if EG_USE_SSE2
inline bool eg_gate_A_sse2(const unsigned char *cnt)
{
	const __m128i a = _mm_set1_epi8(0x20), b = _mm_set1_epi8(0x02);
	__m128i acc = _mm_setzero_si128();
	for (int i = 0; i < 80; i += 16)
	{
		// BoardInc::cnt は union の実効アライン 8 byte なので loadu(load は不可)
		const __m128i v = _mm_loadu_si128((const __m128i *)(cnt + i));
		acc = _mm_or_si128(acc, _mm_or_si128(_mm_cmpeq_epi8(v, a), _mm_cmpeq_epi8(v, b)));
	}
	return _mm_movemask_epi8(acc) == 0;
}

inline bool eg_gate_A2_sse2(const unsigned char *cnt)
{
	const __m128i a = _mm_set1_epi8(0x20), b = _mm_set1_epi8(0x02);
	const __m128i c = _mm_set1_epi8(0x10), d = _mm_set1_epi8(0x01);
	__m128i acc = _mm_setzero_si128();
	for (int i = 0; i < 80; i += 16)
	{
		const __m128i v = _mm_loadu_si128((const __m128i *)(cnt + i));
		acc = _mm_or_si128(acc, _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, a), _mm_cmpeq_epi8(v, b)),
		                                     _mm_or_si128(_mm_cmpeq_epi8(v, c), _mm_cmpeq_epi8(v, d))));
	}
	return _mm_movemask_epi8(acc) == 0;
}
#endif

inline bool endgame_gate_A(const BoardInc &b)
{
#if EG_USE_SSE2
	return eg_gate_A_sse2(b.cnt);
#else
	return eg_gate_A_swar(b.cnt64);
#endif
}

inline bool endgame_gate_A2(const BoardInc &b)
{
#if EG_USE_SSE2
	return eg_gate_A2_sse2(b.cnt);
#else
	return eg_gate_A2_swar(b.cnt64);
#endif
}

// G_T: 空きマス3個以上の柱が高々1本。
// 柱の空きは必ず上から連続するので「空きマス3個以上」⟺「段2 のマスが空」。
inline bool endgame_tall_le1(const Board &b)
{
	const unsigned long long x = ~(b.Me | b.You) & EG_MASK_2;
	return (x & (x - 1)) == 0uLL;      // 立っているビットが 0 個または 1 個
}

// 手数に応じてゲートを切り替える(証明可能な範囲 turn >= 59 に一致させる)。
//   64 / 63 … ゲート不要(R2 は無条件に厳密)
//   62 / 61 … G_A
//   60      … G_A2
//   59      … G_A2 かつ G_T
//   <= 58   … 使わない(実測では誤り 0 だが証明が無く通過率も 1.3% 以下)
inline bool endgame_gate(const BoardInc &b, const int turn)
{
	if (turn >= 63) return true;
	if (turn >= 61) return endgame_gate_A(b);
	if (turn == 60) return endgame_gate_A2(b);
	if (turn == 59) return endgame_gate_A2(b) && endgame_tall_le1(b.b);
	return false;
}

// ---------------------------------------------------------------- 自己検査用の厳密解

// 手番視点で +1(勝ち) / 0(引き分け) / -1(負け)を返す素朴な全読み。
// 打ち切り機構を一切使わないので、-DEG_SELFCHECK の照合基準に使える。
// 研究/verify/endgame_verify.cpp の solve() と同一のアルゴリズム。
inline int endgame_solve_exact(const Board &b)
{
	unsigned long long hand = b.valid_move();
	if (!hand) return 0;
	const unsigned long long rMe = Board::reach(b.Me) & ~b.You;
	if (hand & rMe) return +1;
	const unsigned long long rYou = Board::reach(b.You) & ~b.Me;
	if (hand & rYou)
	{
		if (__builtin_popcountll(hand & rYou) > 1) return -1;   // 二重脅威は防げない
		hand &= rYou;                                          // 阻止一手に強制
	}
	int best = -1;
	while (hand)
	{
		const unsigned long long bit = hand & -hand;
		hand ^= bit;
		const int v = -endgame_solve_exact(b.place_fast_clone(bit));
		if (v > best) best = v;
		if (best == 1) break;
	}
	return best;
}
