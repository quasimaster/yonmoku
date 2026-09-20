#pragma once

#include "board_inc.hpp"   // BoardInc / SQ_LINES / init_sq_lines(無変更で流用)

// board_inc.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md §4.3)。
// 流用元 BoardInc を継承し、cnt[] の「向き」だけを変える。レイアウト(Board 16 B + cnt 80 B)は同一なので
// endgame_exact.hpp のゲート(const BoardInc& を取る)にそのまま渡せる。
//
//   USE_FIXCNT = 1 : cnt[i] = (黒(先手)石数 << 4) | 白(後手)石数 に固定する。
//                    手番が替わっても cnt は入れ替えないので、place_fast_clone のニブル交換 SWAR(u64×10)が不要になる。
//                    評価側は白番ノード(Me = 白)で「ニブル交換済みの表」を引く(evaluate_alpha_inc_tbl_w2.hpp)。
//                    ゲート G_A / G_A2 の判定値集合 {0x20,0x02} / {0x20,0x02,0x10,0x01} はニブル交換に対して対称なので影響を受けない。
//   USE_FIXCNT = 0 : 流用元と同一(cnt[i] = (Me 石数 << 4) | You 石数)。A/B 用。
#ifndef USE_FIXCNT
#define USE_FIXCNT 1
#endif

// 「cnt の上位ニブルが You(= 白が手番)」かどうか。石数が奇数なら白番。
inline bool board_inc2_swapped(const Board& b)
{
	return __builtin_parityll(b.Me | b.You) != 0;
}

struct BoardInc2 : BoardInc
{
	// root で1回だけ全76ライン集計して構築
	static BoardInc2 from(const Board& src)
	{
		BoardInc2 r;
		r.b = src;
		memset(r.cnt, 0, sizeof(r.cnt));   // パディング領域も 0 初期化(SWAR/検証のため)
#if USE_FIXCNT
		const bool swp = board_inc2_swapped(src);                  // 白番なら Me = 白
		const unsigned long long B = swp ? src.You : src.Me;       // 黒石
		const unsigned long long W = swp ? src.Me  : src.You;      // 白石
		for (int i = 0; i < LINES_NUM; i++)
			r.cnt[i] = (unsigned char)(__builtin_popcountll(B & LINES[i]) << 4
			                         | __builtin_popcountll(W & LINES[i]));
#else
		for (int i = 0; i < LINES_NUM; i++)
			r.cnt[i] = (unsigned char)(__builtin_popcountll(src.Me  & LINES[i]) << 4
			                         | __builtin_popcountll(src.You & LINES[i]));
#endif
		return r;
	}

	BoardInc2 place_fast_clone(unsigned long long bit) const
	{
		BoardInc2 r = *this;
		r.b.Me |= bit;
		swap(r.b.Me, r.b.You);
		const int sq = __builtin_ctzll(bit);
#if USE_FIXCNT
		// 着手側(= 置く前の Me)が黒なら上位ニブル、白なら下位ニブルを +1。ニブル交換は不要
		const unsigned char inc = board_inc2_swapped(b) ? 0x01 : 0x10;
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += inc;
#else
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += 0x10;  // Me 側 +1
		// Me/You スワップに合わせて全ラインのニブルを交換(80B = u64×10 の SWAR)
		for (int i = 0; i < 10; i++)
			r.cnt64[i] = (r.cnt64[i] & 0xF0F0F0F0F0F0F0F0uLL) >> 4 | (r.cnt64[i] & 0x0F0F0F0F0F0F0F0FuLL) << 4;
#endif
		return r;
	}
};

// デバッグ検証: cnt が b から再構築した値と一致するか(#ifndef NDEBUG の assert 用)
inline bool board_inc2_consistent(const BoardInc2& bi)
{
	const BoardInc2 r = BoardInc2::from(bi.b);
	return memcmp(r.cnt, bi.cnt, sizeof(r.cnt)) == 0;
}
