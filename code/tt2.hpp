#pragma once

#include <memory>
#include <cstdint>

#include "tt.hpp"   // TTEntry / TTBound / TT_NO_MOVE / TT_EMPTY / g_node_count / TranspositionTable::hash(無変更で流用)

// tt.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md §9.5)。
// エントリ構造(16 B)・総エントリ数・ハッシュ・世代管理は流用元と同一で、差分は次の 2 点。
//
//   USE_TT_BUCKET = N(既定 4): 隣接 N エントリを 1 バケットにする(4 × 16 B = 64 B = 1 キャッシュライン)。
//       probe はバケット内を順に見る。store は「空き or 同一局面」があればそこへ、無ければ
//       「旧世代を優先、同世代なら最も浅いもの」を追い出して【必ず】格納する。
//       ※ 流用元の 1 way は別局面なら無条件に上書きするので、深い結果が浅い葉の格納で消える。
//       ※ 「同世代の深いエントリより浅ければ格納しない」規則は重い局で逆効果になる(設計書 §9.4)。採らない。
//       ※ 置換表の中身が変わるので探索ノード数は変わる。root 評価値・最善手集合は実測 606 手番で不変だったが、保証は無い。
//   USE_TT_BUCKET = 1: 流用元と完全同一の probe / store(A/B 用)。
//
//   表は 64 B 境界に揃えて確保する(std::vector では揃わない)。また流用元は「値初期化で 64 MB をゼロ埋め → bound を全走査」と
//   2 回書いていたのを、new TTEntry[](トリビアル型なので未初期化)+ bound だけの 1 回書きにした(設計書 §4.5)。
#ifndef USE_TT_BUCKET
#define USE_TT_BUCKET 4
#endif
static_assert(USE_TT_BUCKET == 1 || USE_TT_BUCKET == 2 || USE_TT_BUCKET == 4 || USE_TT_BUCKET == 8,
              "USE_TT_BUCKET must be 1, 2, 4 or 8");

struct TranspositionTable2
{
	std::unique_ptr<TTEntry[]> storage;   // 64 B 揃え用に 4 エントリ余分に確保
	TTEntry* table;
	unsigned long long mask;
	unsigned char generation = 0;
	static constexpr unsigned long long BK = USE_TT_BUCKET;

	explicit TranspositionTable2(int bits = 22)   // 2^22 entry = 64MB
		: storage(new TTEntry[(1uLL << bits) + 4]), mask((1uLL << bits) - 1)
	{
		uintptr_t p = (uintptr_t)storage.get();
		p = (p + 63) & ~(uintptr_t)63;
		table = (TTEntry*)p;
		// 空盤面 (Me=You=0) の hash が 0 になるため key==0 では未使用判定できない(流用元と同じ)
		for (unsigned long long i = 0; i <= mask; i++) table[i].bound = TT_EMPTY;
	}

	static inline unsigned long long hash(const Board& b) { return TranspositionTable::hash(b); }

	void new_search() { generation++; }   // move() 毎に呼ぶ(表クリア不要)

#if USE_TT_BUCKET > 1
	const TTEntry* probe(unsigned long long key) const
	{
		const TTEntry* e = &table[key & mask & ~(BK - 1)];
		for (unsigned long long k = 0; k < BK; k++)
			if (e[k].key == key && e[k].bound != TT_EMPTY) return &e[k];
		return nullptr;
	}

	void store(unsigned long long key, int value, int depth,
	           unsigned char bound, unsigned char best_move)
	{
		TTEntry* e = &table[key & mask & ~(BK - 1)];
		TTEntry* t = nullptr;
		for (unsigned long long k = 0; k < BK && !t; k++)
			if (e[k].bound == TT_EMPTY || e[k].key == key) t = &e[k];   // 空き or 同一局面
		if (!t)
		{	// 全部別局面: 旧世代を優先して追い出し、同世代なら最も浅いものを追い出す。必ず格納する
			t = &e[0];
			for (unsigned long long k = 1; k < BK; k++)
			{
				const bool oldt = t->age != generation, oldk = e[k].age != generation;
				if (oldk != oldt) { if (oldk) t = &e[k]; }
				else if (e[k].depth < t->depth) t = &e[k];
			}
		}
		*t = TTEntry{key, value, (signed char)depth, bound, best_move, generation};
	}
#else
	// 流用元 tt.hpp:52-66 と同一
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
#endif
};
