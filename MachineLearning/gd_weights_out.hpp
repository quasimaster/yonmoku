#pragma once

#include "../code/common.hpp"

// 勾配降下法の結果(bestOne[0..28] × 先手 4 バケット + 後手 4 バケット)を
// weights/verX_Y.txt と同じ書式で出力する。
//
// 出力書式は code/eval_weights.hpp の dump_eval_weights() と完全に同じにしてある
// (キー名を 17 文字へ空白詰め → " = " → 値をカンマ区切り、セクション前に空行)。
// そのため、この出力をそのままファイルへ貼れば
//   ./match_weights weights/verX_Y.txt ...
// などがそのまま読める。
//
// 添字と各キーの対応は code/eval_weights.hpp の SideWeights のコメント、および
// code/evaluate_alpha_t_w.hpp / code/evaluate_alpha_inc_tbl_w.hpp の参照箇所と
// 突き合わせて確認済み。対応表は下記 side_section() のコメントを参照。

namespace gdout
{

// bestOne[0..28] の意味(特徴量構築部 ps[0..28] と同一)
//   [0..3]   pb, pc, pd, pe    基礎点     -> stdweight        = 0,pb,pc,0,pd,pe,0
//   [4..6]   pg, ph, pi        layer_me   -> layer_me         = pg,ph,pi
//   [7..9]   pj, pk, pl        layer_you  -> layer_you        = pj,pk,pl
//   [10..13] pm, pn, pr, pt    交点       -> intersection     = pm,pn,pr,pt
//   [14]     po                連続       -> continuous       = po
//   [15..18] ppa..ppd          makeT Me   -> maketweight[0..3]
//   [19..22] pqa..pqd          makeT You  -> maketweight[4..7]
//   [23..25] ppe, ppf, ppg     連続 makeT Me  -> conti_maketweight[0..2]
//   [26..28] pqe, pqf, pqg     連続 makeT You -> conti_maketweight[3..5]

// dump_eval_weights() と同じ行整形。
inline void put_key(ostream &os, const char *key, const vector<int> &v)
{
	string k = key;
	k.resize(17, ' ');            // 桁揃え(conti_maketweight が最長 17 文字)
	os << k << " = ";
	for (size_t j = 0; j < v.size(); j++) { if (j) os << ","; os << v[j]; }
	os << "\n";
}

// 1 バケット分(= 32 個の整数)を 7 行で書き出す。
inline void put_bucket(ostream &os, const char *side, int bucket, const int w[29])
{
	os << "\n[" << side << ".bucket" << bucket << "]\n";
	put_key(os, "stdweight",         {0, w[0], w[1], 0, w[2], w[3], 0});
	put_key(os, "maketweight",       {w[15], w[16], w[17], w[18], w[19], w[20], w[21], w[22]});
	put_key(os, "conti_maketweight", {w[23], w[24], w[25], w[26], w[27], w[28]});
	put_key(os, "layer_me",          {w[4], w[5], w[6]});
	put_key(os, "layer_you",         {w[7], w[8], w[9]});
	put_key(os, "intersection",      {w[10], w[11], w[12], w[13]});
	put_key(os, "continuous",        {w[14]});
}

// 学習時の loss を # コメント行として書き出す。
//
// パーサ code/eval_weights.hpp:209-210 は '#' 以降を行末まで捨てるので、
// この行がいくつ増えても既存の読み込み側(match_weights など)は影響を受けない。
// 逆に言うと、値を残せる場所として使えるのは # の後ろだけである。
//
// long double を printf 系へ渡すと MinGW では %Lf が正しく扱われないことがあるため、
// double へ落としてから整形する。loss は 1e4~1e5 の大きさなので
// double の有効桁(約 15 桁)で足り、小数 3 桁の表示には十分。
inline void put_loss_comments(ostream &os, const long double *fir_loss, const long double *sec_loss)
{
	if (!fir_loss && !sec_loss) return;

	os << "#\n";
	os << "# 学習時の loss(交差エントロピーの総和。小さいほど教師値に近い)\n";
	os << "# 同じ側・同じバケット同士でのみ比較できる(対象の局面数が違えば大きさも変わる)\n";
	for (int s = 0; s < 2; s++)
	{
		const long double *L = (s == 0) ? fir_loss : sec_loss;
		if (!L) continue;
		const char *side = (s == 0) ? "fir" : "sec";
		const int base = (s == 0) ? 4 : 5;   // bucket0 の開始 turn(weights/README.md の turn_bucket)
		for (int b = 0; b < 4; b++)
		{
			char buf[128];
			if (L[b] >= (long double)INF)
			{
				// INF(= 1e9、code/common.hpp:37)のままなら一度も更新されなかったということ。
				// 数値として書くと本物の loss と紛れるので文字で書く。
				snprintf(buf, sizeof(buf), "# loss  %s.bucket%d (turn %2d~%2d) = ----- (改善なし)",
				         side, b, base + 14 * b, base + 13 + 14 * b);
			}
			else
			{
				snprintf(buf, sizeof(buf), "# loss  %s.bucket%d (turn %2d~%2d) = %.3f",
				         side, b, base + 14 * b, base + 13 + 14 * b, (double)L[b]);
			}
			os << buf << "\n";
		}
	}
}

// weights/verX_Y.txt そのものを出力する。fir[4][29] / sec[4][29] はバケット順。
//
// fir_loss / sec_loss(各 4 要素)を渡すと、name: 行の直後へ loss を # コメントで追加する。
// 省略すれば出力は dump_eval_weights() と 1 バイト単位で同じままなので、
// 書式一致を確かめる tools/verify_weights_format.cpp はそのまま通る。
inline void dump_weights_file(ostream &os, const string &name,
                              const int fir[4][29], const int sec[4][29],
                              const long double *fir_loss = nullptr,
                              const long double *sec_loss = nullptr)
{
	os << "# 立体四目並べ 評価関数重み\n";
	os << "version: 1\n";
	os << "name: " << (name.empty() ? string("unnamed") : name) << "\n";
	put_loss_comments(os, fir_loss, sec_loss);
	for (int b = 0; b < 4; b++) put_bucket(os, "fir", b, fir[b]);
	for (int b = 0; b < 4; b++) put_bucket(os, "sec", b, sec[b]);
}

}// namespace gdout
