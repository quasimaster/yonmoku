// =============================================================================
//  board_inc2.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  board_inc.hpp の BoardInc を高速化した BoardInc2。
//  (設計: docs/設計書/高速化/speedup-proposal-main-core.md §4.3)
//
//  ■ BoardInc のおさらい
//    BoardInc は盤面 b(Board)に加えて、76本の勝ちラインごとの石数 cnt[i] を持つ。
//    cnt[i] は 1バイトで、上位 4 bit(上位ニブル)と下位 4 bit(下位ニブル)に石数を入れる。
//      流用元 BoardInc : cnt[i] = (Me の石数 << 4) | You の石数
//    Me と You は着手のたびに入れ替わるので、流用元では着手のたびに
//    76本ぶんのニブルを全部入れ替える必要があった(SWAR で u64×10 回)。
//
//  ■ BoardInc2 の工夫(USE_FIXCNT = 1)
//    ニブルの向きを手番ではなく色で固定する。
//      BoardInc2       : cnt[i] = (白(先手)の石数 << 4) | 黒(後手)の石数
//    こうすると手番が替わっても cnt を入れ替えなくてよい。
//    その代わり評価側は、黒番の局面(Me = 黒)では「ニブルを入れ替えておいた表」を引く
//    (evaluate_alpha_inc_tbl_w2.hpp)。
//    終盤のゲート G_A / G_A2 が見る値の集合 {0x20, 0x02} / {0x20, 0x02, 0x10, 0x01} は
//    ニブルを入れ替えても変わらないので、この変更の影響を受けない。
//
//  ■ レイアウト
//    メンバは BoardInc と同じ(Board 16 B + cnt 80 B)。継承しているだけなので、
//    const BoardInc& を受け取る endgame_exact.hpp のゲートにそのまま渡せる。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
//    from() の中のローカル変数 B / W は、色の入れ替えに合わせて W(白石)/ B(黒石)と名前を入れ替えた。
// =============================================================================
#pragma once

#include "board_inc.hpp"   // BoardInc / SQ_LINES / init_sq_lines(無変更で流用)

// USE_FIXCNT = 1 : cnt のニブルの向きを色で固定する(既定。上の説明を参照)。
// USE_FIXCNT = 0 : 流用元と同じ向き(cnt[i] = (Me の石数 << 4) | You の石数)。新旧の比較(A/B)用。
#ifndef USE_FIXCNT
#define USE_FIXCNT 1
#endif

// 「cnt の上位ニブルが You か」、つまり「いま黒が手番か」を返す。
// 盤上の石の総数が奇数なら黒番(白が先手なので、白が置いた直後は奇数になる)。
inline bool board_inc2_swapped(const Board& b)
{
	return __builtin_parityll(b.Me | b.You) != 0;
}

struct BoardInc2 : BoardInc
{
	// 探索の根(root)で 1回だけ呼び、76本すべてのラインの石数を数えて作る。
	// 子局面は place_fast_clone() で差分更新するので、この全集計は根でしか行わない。
	static BoardInc2 from(const Board& src)
	{
		BoardInc2 r;
		r.b = src;
		memset(r.cnt, 0, sizeof(r.cnt));   // 配列末尾の詰め物(パディング)も 0 にする(SWAR と検証で比較するため)
#if USE_FIXCNT
		const bool swp = board_inc2_swapped(src);                  // 黒番なら Me = 黒
		const unsigned long long W = swp ? src.You : src.Me;       // 白石
		const unsigned long long B = swp ? src.Me  : src.You;      // 黒石
		for (int i = 0; i < LINES_NUM; i++)
			r.cnt[i] = (unsigned char)(__builtin_popcountll(W & LINES[i]) << 4
			                         | __builtin_popcountll(B & LINES[i]));
#else
		for (int i = 0; i < LINES_NUM; i++)
			r.cnt[i] = (unsigned char)(__builtin_popcountll(src.Me  & LINES[i]) << 4
			                         | __builtin_popcountll(src.You & LINES[i]));
#endif
		return r;
	}

	// 合法手 bit に手番側の石を置いた子局面を返す(元の局面は変えない)。
	// cnt は、置いたマスを通るライン(SQ_LINES[sq] に並ぶ。末尾は 0xFF)だけを +1 する。
	BoardInc2 place_fast_clone(unsigned long long bit) const
	{
		BoardInc2 r = *this;
		r.b.Me |= bit;
		swap(r.b.Me, r.b.You);
		const int sq = __builtin_ctzll(bit);   // bit の位置 = 置いたマスの番号
#if USE_FIXCNT
		// 置いた側(= 置く前の Me)が白なら上位ニブル、黒なら下位ニブルを +1 する。ニブルの入れ替えは要らない。
		const unsigned char inc = board_inc2_swapped(b) ? 0x01 : 0x10;
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += inc;
#else
		for (const unsigned char* p = SQ_LINES[sq]; *p != 0xFF; p++) r.cnt[*p] += 0x10;  // Me 側を +1
		// Me と You を入れ替えたので、全ラインのニブルも入れ替える(80 B を u64×10 個として SWAR で処理)。
		//   上位ニブル(0xF0...)を 4 bit 右へ、下位ニブル(0x0F...)を 4 bit 左へ動かして OR する。
		for (int i = 0; i < 10; i++)
			r.cnt64[i] = (r.cnt64[i] & 0xF0F0F0F0F0F0F0F0uLL) >> 4 | (r.cnt64[i] & 0x0F0F0F0F0F0F0F0FuLL) << 4;
#endif
		return r;
	}
};

// デバッグ用の検証: 差分更新してきた cnt が、盤面 b から数え直した値と一致するかを返す。
// (NDEBUG が定義されていないときの assert から呼ぶ)
inline bool board_inc2_consistent(const BoardInc2& bi)
{
	const BoardInc2 r = BoardInc2::from(bi.b);
	return memcmp(r.cnt, bi.cnt, sizeof(r.cnt)) == 0;
}
