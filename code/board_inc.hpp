#pragma once

#include <cstring>

#include "common.hpp"
#include "board.hpp"

// 提案7c: ライン充填数の増分更新(implementation-plan-eval-speedup.md §3.3)。
// 探索内部専用の BoardInc(Board + ライン充填数 80 byte)を導入し、
// 葉評価の board.count()(76 ライン × AND/popcount)を配列参照に置き換える。
// Game/Player の境界は Board のままとし、move() の先頭で一度だけ変換する。

// マス sq を通るライン番号(4〜7本)。0xFF 終端。init_lines() の後に init_sq_lines() を呼ぶこと。
inline unsigned char SQ_LINES[64][8];

inline void init_sq_lines()
{
	int total = 0;
	for (int sq = 0; sq < 64; sq++)
	{
		int n = 0;
		for (int i = 0; i < LINES_NUM; i++)
			if (LINES[i] >> sq & 1) SQ_LINES[sq][n++] = (unsigned char)i;
		assert(n >= 4 && n <= 7);
		total += n;
		for (; n < 8; n++) SQ_LINES[sq][n] = 0xFF;
	}
	assert(total == LINES_NUM * 4);   // 76 本 × 4 マス = 304
	(void)total;
}

struct BoardInc
{
	Board b;                     // 16 byte(Me, You)
	union
	{
		unsigned char cnt[80];       // ライン充填数。上位ニブル=Me 石数、下位=You 石数。76本+SWAR 用パディング4
		unsigned long long cnt64[10];// ニブル交換 SWAR 用ビュー
	};
	// 合計 96 byte

	// root で1回だけ全76ライン集計して構築
	static BoardInc from(const Board& src)
	{
		BoardInc r;
		r.b = src;
		memset(r.cnt, 0, sizeof(r.cnt));   // パディング領域も 0 初期化(SWAR/検証のため)
		for (int i = 0; i < LINES_NUM; i++)
			r.cnt[i] = (unsigned char)(__builtin_popcountll(src.Me  & LINES[i]) << 4
			                         | __builtin_popcountll(src.You & LINES[i]));
		return r;
	}

	BoardInc place_fast_clone(unsigned long long bit) const
	{
		BoardInc r = *this;
		r.b.Me |= bit;
		swap(r.b.Me, r.b.You);
		const int sq = __builtin_ctzll(bit);
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += 0x10;  // Me 側 +1
		// Me/You スワップに合わせて全ラインのニブルを交換(80B = u64×10 の SWAR)
		for (int i = 0; i < 10; i++)
			r.cnt64[i] = (r.cnt64[i] & 0xF0F0F0F0F0F0F0F0uLL) >> 4 | (r.cnt64[i] & 0x0F0F0F0F0F0F0F0FuLL) << 4;
		return r;
	}

	// Board への転送(ai_player 側の読み替えを最小にするため)
	int turn() const { return b.turn(); }
	unsigned long long valid_move() const { return b.valid_move(); }
};

// デバッグ検証: cnt が b から再構築した値と一致するか(#ifndef NDEBUG の assert 用)
inline bool board_inc_consistent(const BoardInc& bi)
{
	const BoardInc r = BoardInc::from(bi.b);
	return memcmp(r.cnt, bi.cnt, sizeof(r.cnt)) == 0;
}
