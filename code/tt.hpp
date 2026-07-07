#pragma once
#include "common.hpp"
#include "board.hpp"

#ifdef BENCH
inline thread_local long long g_node_count = 0;
#endif

enum TTBound : unsigned char { TT_EXACT = 0, TT_LOWER = 1, TT_UPPER = 2 };
const unsigned char TT_NO_MOVE = 0xFF;
const unsigned char TT_EMPTY = 0xFF;

struct TTEntry            // 16 byte
{
	unsigned long long key;   // 検証用フルキー(8B)
	int value;                // 探索値(4B)
	signed char depth;        // 格納時の残り深さ level(1B)
	unsigned char bound;      // TTBound / TT_EMPTY(1B)
	unsigned char best_move;  // マス番号 0..63 / TT_NO_MOVE(1B)
	unsigned char age;        // 世代(1B)
};
static_assert(sizeof(TTEntry) == 16, "TTEntry must be 16 bytes");

struct TranspositionTable
{
	vector<TTEntry> table;
	unsigned long long mask;
	unsigned char generation = 0;

	explicit TranspositionTable(int bits = 22)   // 2^22 entry = 64MB
		: table(1uLL << bits), mask((1uLL << bits) - 1)
	{
		// 空盤面 (Me=You=0) の hash が 0 になるため key==0 では未使用判定できない
		for (TTEntry& e : table) e.bound = TT_EMPTY;
	}

	// splitmix64 の finalizer。(Me, You) 128bit → 64bit key
	static inline unsigned long long mix(unsigned long long x)
	{
		x ^= x >> 30; x *= 0xbf58476d1ce4e5b9uLL;
		x ^= x >> 27; x *= 0x94d049bb133111ebuLL;
		x ^= x >> 31;
		return x;
	}
	static inline unsigned long long hash(const Board& b)
	{
		return mix(b.Me) ^ (mix(b.You) * 0x9e3779b97f4a7c15uLL);
	}

	void new_search() { generation++; }   // move() 毎に呼ぶ(表クリア不要)

	const TTEntry* probe(unsigned long long key) const
	{
		const TTEntry& e = table[key & mask];
		return (e.key == key && e.bound != TT_EMPTY) ? &e : nullptr;
	}

	void store(unsigned long long key, int value, int depth,
	           unsigned char bound, unsigned char best_move)
	{
		TTEntry& e = table[key & mask];
		// 置換規則: 空 or 別局面 or 旧世代 or 同等以上の深さ なら上書き
		if (e.bound == TT_EMPTY || e.key != key || e.age != generation || depth >= e.depth)
			e = TTEntry{key, value, (signed char)depth, bound, best_move, generation};
	}
};
