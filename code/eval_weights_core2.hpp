#pragma once

#include "eval_weights_core.hpp"   // EvalWeightsCore / EvalWeights / flag_tbl / init_flag_tbl(無変更で流用)
#include "board_inc2.hpp"          // USE_FIXCNT

// eval_weights_core.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md §4.3)。
// EvalWeightsCore を継承し、「添字をニブル交換した stdweight 表」を足しただけ。
// 重みファイルの形式・読み込み・組み込み既定値は流用元と同一(load / builtin を薄く包む)。
//
// USE_FIXCNT = 1 のとき、白番ノードでは BoardInc2::cnt の向き(黒<<4|白)が Me/You と逆になるので、
//   stdweight_*_tbl_sw[b][idx] = stdweight_*_tbl[b][swap(idx)]  (swap = ニブル交換)
// を引けば流用元と同じ値になる。flag_tbl も同様に flag_tbl_sw を持つ。
// USE_FIXCNT = 0 のときは使われない(表は構築だけする)。

inline constexpr unsigned eval_swap_nibble(unsigned b) { return (b >> 4) | ((b & 15) << 4); }

alignas(64) inline unsigned char flag_tbl_sw[256];   // flag_tbl_sw[idx] = flag_tbl[swap(idx)]

// 流用元 init_eval_tbl() の置き換え(flag_tbl + flag_tbl_sw)
inline void init_eval_tbl2()
{
	init_flag_tbl();
	for (int idx = 0; idx < 256; idx++) flag_tbl_sw[idx] = flag_tbl[eval_swap_nibble(idx)];
}

struct EvalWeightsCore2 : EvalWeightsCore
{
	alignas(64) int stdweight_fir_tbl_sw[4][256];   // [bucket][swap(cnt)]
	alignas(64) int stdweight_sec_tbl_sw[4][256];

	void build_sw()
	{
		for (int idx = 0; idx < 256; idx++) for (int b = 0; b < 4; b++)
		{
			stdweight_fir_tbl_sw[b][idx] = base.stdweight_fir_tbl[b][eval_swap_nibble(idx)];
			stdweight_sec_tbl_sw[b][idx] = base.stdweight_sec_tbl[b][eval_swap_nibble(idx)];
		}
	}

	bool load(const string& path, string* err)
	{
		if (!EvalWeightsCore::load(path, err)) return false;
		build_sw();
		return true;
	}

	static const EvalWeightsCore2& builtin()   // base = ver7.2、core = 0(流用元と同じ)
	{
		static const EvalWeightsCore2 W = []()
		{
			EvalWeightsCore2 w{};
			static_cast<EvalWeightsCore&>(w) = EvalWeightsCore::builtin();
			w.build_sw();
			return w;
		}();
		return W;
	}
};
