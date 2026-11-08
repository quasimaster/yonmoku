// =============================================================================
//  board_inc.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  探索の内部だけで使う盤面 BoardInc。Board に「76本のラインそれぞれの石の数」を足したもの。
//
//  ■ なぜ必要か
//    評価関数は葉の局面ごとに 76本すべてのラインの石の数を使う。
//    Board::count() で毎回数え直すと「76 ライン × AND + popcount」かかる。
//    しかし 1手で石の数が変わるのは、置いたマスを通るライン(4〜7本)だけである。
//    そこで石の数を配列 cnt[] に持っておき、着手のたびにその数本だけを足す(差分更新)。
//
//  ■ 使い方
//    対局(Game / Player)とのやり取りは今までどおり Board で行い、
//    探索の入口(AI の move() の先頭)で一度だけ BoardInc::from() で変換する。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================

#pragma once

#include <cstring>   // memset / memcmp

#include "common.hpp"
#include "board.hpp"

// 提案7c: ライン充填数の増分更新(implementation-plan-eval-speedup.md §3.3)。
// 探索内部専用の BoardInc(Board + ライン充填数 80 byte)を導入し、
// 葉評価の board.count()(76 ライン × AND/popcount)を配列参照に置き換える。
// Game/Player の境界は Board のままとし、move() の先頭で一度だけ変換する。

// マス sq を通るライン番号(4〜7本)。0xFF 終端。init_lines() の後に init_sq_lines() を呼ぶこと。
//   SQ_LINES[sq] = { ライン番号, ライン番号, ..., 0xFF(終わりの印), ... }
// 1マスを通るラインは、端のマスで 4本(縦・x・y + 斜め 1本)、
// 立体の対角線上のマス(隅と中央)で 7本(縦・x・y・平面の斜め 3本・立体の対角線 1本)。
inline unsigned char SQ_LINES[64][8];

// SQ_LINES を LINES から作る。
inline void init_sq_lines()
{
	int total = 0;
	for (int sq = 0; sq < 64; sq++)
	{
		int n = 0;
		// マス sq のビットを含むラインの番号を順に書き込む。
		for (int i = 0; i < LINES_NUM; i++)
			if (LINES[i] >> sq & 1) SQ_LINES[sq][n++] = (unsigned char)i;
		assert(n >= 4 && n <= 7);
		total += n;
		// 残りを 0xFF で埋める(読む側はここで止まる)。
		for (; n < 8; n++) SQ_LINES[sq][n] = 0xFF;
	}
	// 1本のラインは 4マスを通るので、全マスで数えた合計は 76 × 4 = 304 になるはず。
	assert(total == LINES_NUM * 4);   // 76本 × 4マス = 304
	(void)total;   // NDEBUG で assert が消えたときの「未使用変数」警告を抑える
}

struct BoardInc
{
	Board b;                     // 16 byte(Me, You)
	// cnt[i] … ライン i の石の数を 1 byte に詰めたもの。
	//   上位 4 bit(ニブル)= 手番側 Me の石の数(0〜4)
	//   下位 4 bit         = 相手 You の石の数(0〜4)
	//   例: 0x20 = 手番側だけ 2個、0x11 = 両者 1個ずつ(死んだライン)。
	// union なので、同じ 80 byte を 8 byte × 10個(cnt64)としても読み書きできる。
	// 76本では 8 の倍数にならないので、4 byte の詰め物(パディング)を足して 80 byte にしている。
	union
	{
		unsigned char cnt[80];       // ライン充填数。上位ニブル=Me 石数、下位=You 石数。76本+SWAR 用パディング4
		unsigned long long cnt64[10];// ニブル交換 SWAR 用ビュー
	};
	// 合計 96 byte

	// root で1回だけ全76ライン集計して構築
	// 通常の Board から BoardInc を作る。全ラインを数えるので重いが、探索の最初に 1回だけ呼ぶ。
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

	// -------------------------------------------------------------------------
	//  place_fast_clone(bit): Board::place_fast_clone と同じく石を置いて手番を替えた新盤面を返す。
	//  あわせて cnt[] を差分更新する。
	//    1. 置いたマスを通るライン(SQ_LINES)の上位ニブル(= 置いた側 Me)に 1 を足す(+0x10)
	//    2. Me と You を入れ替えたので、全ラインの上位・下位ニブルも入れ替える
	//  2 は 1 byte ずつやると 76回かかるので、8 byte ずつ 10回でまとめて行う(SWAR)。
	//    (x & 0xF0F0...) >> 4 … 各 byte の上位ニブルを下位へ
	//    (x & 0x0F0F...) << 4 … 各 byte の下位ニブルを上位へ
	//  SWAR = SIMD Within A Register(1つのレジスタ内で複数のデータを同時に処理する技法)。
	// -------------------------------------------------------------------------
	BoardInc place_fast_clone(unsigned long long bit) const
	{
		BoardInc r = *this;
		r.b.Me |= bit;
		swap(r.b.Me, r.b.You);
		// 置いたマスの番号(ビット位置)。__builtin_ctzll は下位から続く 0 の数 = 最下位 1 の位置。
		const int sq = __builtin_ctzll(bit);
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += 0x10;  // Me 側 +1
		// Me/You スワップに合わせて全ラインのニブルを交換(80B = u64×10 の SWAR)
		for (int i = 0; i < 10; i++)
			r.cnt64[i] = (r.cnt64[i] & 0xF0F0F0F0F0F0F0F0uLL) >> 4 | (r.cnt64[i] & 0x0F0F0F0F0F0F0F0FuLL) << 4;
		return r;
	}

	// Board への転送(ai_player 側の読み替えを最小にするため)
	// 探索コードが Board と同じ書き方で呼べるよう、よく使う 2つを中の Board に任せる。
	int turn() const { return b.turn(); }
	unsigned long long valid_move() const { return b.valid_move(); }
};

// デバッグ検証: cnt が b から再構築した値と一致するか(#ifndef NDEBUG の assert 用)
// 差分更新を積み重ねた cnt[] が、盤面から数え直した値と一致するかを比べる(バグ検出用)。
inline bool board_inc_consistent(const BoardInc& bi)
{
	const BoardInc r = BoardInc::from(bi.b);
	return memcmp(r.cnt, bi.cnt, sizeof(r.cnt)) == 0;
}
