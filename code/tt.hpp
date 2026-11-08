// =============================================================================
//  tt.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  置換表(transposition table)。探索で一度調べた局面の結果を覚えておき、
//  別の手順で同じ局面に来たときに再利用する表である。
//    - 1エントリ 16 B、既定で 2^22 エントリ(64 MB)
//    - 局面(Me, You)を 64 bit のキーに変換し、キーの下位ビットで表の位置を決める(1 way)
//    - 探索のたびに世代(generation)を 1 増やし、古い結果を優先して上書きする
//  ai_player_pvs_inc_id.hpp が使う。高速化版は tt2.hpp。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once
#include "common.hpp"
#include "board.hpp"

// -DBENCH でビルドしたときだけ、探索したノード数を数える(スレッドごとに別の変数)。
#ifdef BENCH
inline thread_local long long g_node_count = 0;
#endif

// 格納した値の種類(αβ探索の値は、窓の外に出ると「下限」や「上限」しか分からない)。
//   TT_EXACT : 正確な値
//   TT_LOWER : 下限(β カットが起きた。本当の値はこれ以上)
//   TT_UPPER : 上限(どの手も α を超えなかった。本当の値はこれ以下)
enum TTBound : unsigned char { TT_EXACT = 0, TT_LOWER = 1, TT_UPPER = 2 };
const unsigned char TT_NO_MOVE = 0xFF;   // 最善手が無い(記録していない)ことを表す値
const unsigned char TT_EMPTY = 0xFF;     // bound に入れて「未使用のエントリ」を表す値

struct TTEntry            // 16 byte
{
	unsigned long long key;   // 検証用のキー全体(8 B)。表の位置が同じ別局面と区別する
	int value;                // 探索で得た値(4 B)
	signed char depth;        // 格納したときの残りの深さ level(1 B)
	unsigned char bound;      // TTBound、または未使用を表す TT_EMPTY(1 B)
	unsigned char best_move;  // 最善手のマス番号 0..63、または TT_NO_MOVE(1 B)
	unsigned char age;        // 格納したときの世代(1 B)
};
static_assert(sizeof(TTEntry) == 16, "TTEntry must be 16 bytes");

struct TranspositionTable
{
	vector<TTEntry> table;
	unsigned long long mask;          // 表の位置 = key & mask(表の大きさは 2 のべき乗)
	unsigned char generation = 0;     // 現在の世代

	explicit TranspositionTable(int bits = 22)   // 2^22 entry = 64MB
		: table(1uLL << bits), mask((1uLL << bits) - 1)
	{
		// 空の盤面(Me = You = 0)のキーは 0 になる。そのため「key == 0 なら未使用」とは判定できず、
		// bound に TT_EMPTY を入れて未使用を表す。
		for (TTEntry& e : table) e.bound = TT_EMPTY;
	}

	// splitmix64 の最後の混ぜ合わせ処理。入力の各ビットが出力の全ビットに広がるようにする。
	static inline unsigned long long mix(unsigned long long x)
	{
		x ^= x >> 30; x *= 0xbf58476d1ce4e5b9uLL;
		x ^= x >> 27; x *= 0x94d049bb133111ebuLL;
		x ^= x >> 31;
		return x;
	}
	// 局面(Me, You の 128 bit)を 64 bit のキーにする。
	// You 側には定数を掛けて、Me と You を入れ替えた局面が同じキーにならないようにしている。
	static inline unsigned long long hash(const Board& b)
	{
		return mix(b.Me) ^ (mix(b.You) * 0x9e3779b97f4a7c15uLL);
	}

	void new_search() { generation++; }   // 1手を考えるたび(move() ごと)に呼ぶ。表を消さずに済む

	// key の局面が表にあればそのエントリを、なければ nullptr を返す。
	const TTEntry* probe(unsigned long long key) const
	{
		const TTEntry& e = table[key & mask];
		return (e.key == key && e.bound != TT_EMPTY) ? &e : nullptr;
	}

	// 探索の結果を格納する。
	void store(unsigned long long key, int value, int depth,
	           unsigned char bound, unsigned char best_move)
	{
		TTEntry& e = table[key & mask];
		// 置き換えの規則: 空き、別の局面、古い世代、または同じかより深い探索の結果なら上書きする。
		// (同じ局面・同じ世代で、より浅い結果だけは上書きしない)
		if (e.bound == TT_EMPTY || e.key != key || e.age != generation || depth >= e.depth)
			e = TTEntry{key, value, (signed char)depth, bound, best_move, generation};
	}
};
