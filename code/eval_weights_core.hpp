#pragma once

#include "eval_weights.hpp"   // EvalWeights / SideWeights / evalw::(trim, read_line, parse_ints, store, fetch)
#include "core_feature.hpp"   // core_feat::NUM

// eval_weights.hpp に「核 2 マスの全状態」の重み(core)を足したモデル。
// 設計: docs/設計書/評価関数パラメータ/investigation-new-eval-features.md §2.6 D / §5.1
//
// 既存の EvalWeights は 1 行も変えずに base として丸ごと持つ。
// したがって既存の評価関数(evaluate_alpha_inc_tbl_w.hpp)に base をそのまま渡せ、
// core を全部 0 にすれば既存モデルと完全に同じ評価値になる。
//
// ■ 重みファイル形式(既存形式の上位互換)
//   version: 1  … 既存ファイル(weights/alpha/ver8_2.txt など)。core キーは書けない。core は全部 0 で読む。
//   version: 2  … core キーを 32 セクションすべてに持つ。
//     [fir.bucket0]
//     stdweight         = ...           # 既存 7 キーは version 1 と同一
//     ...
//     core              = a,b,c,d,e,f   # 6 個。core_feature.hpp の out[0..5] の順
//
// ★ファイル入力は eval_weights.hpp と同じく cstdio で行う(MinGW でヘッダ inline 内の
//   std::ifstream 構築が -O1 以上で SEGV するため。eval_weights.hpp 冒頭の注意を参照)。

struct EvalWeightsCore
{
	EvalWeights base;                          // 既存 7 キー(+ name, 派生表)
	int core_fir[4 * core_feat::NUM];          // [bucket*6 + k]  先手用
	int core_sec[4 * core_feat::NUM];          // [bucket*6 + k]  後手用

	bool load(const string& path, string* err);
	static const EvalWeightsCore& builtin();   // base = EvalWeights::builtin()(ver7.2), core = 0
	bool has_core() const;                     // core が 1 つでも非 0 か
};

namespace evalwc
{
	inline constexpr int KEY_CORE = 7;                  // evalw::KEY[0..6] の次
	inline const char* const CORE_KEY = "core";
}

inline bool EvalWeightsCore::has_core() const
{
	for (int i = 0; i < 4 * core_feat::NUM; i++)
		if (core_fir[i] || core_sec[i]) return true;
	return false;
}

// 読み込み処理は EvalWeights::load()(eval_weights.hpp:178-275)と同じ手順で、
// 差分は「core キーを受け付ける」「version 2 を受け付ける」の 2 点だけ。
// 失敗時は false を返し err に「パス:行番号: 理由」を入れる。組み込み既定値へは戻らない。
inline bool EvalWeightsCore::load(const string& path, string* err)
{
	static const char* const prefix[] = {"", "../", "../../"};
	FILE* fp = nullptr;
	string used;
	for (const char* p : prefix)
	{
		used = string(p) + path;
		fp = fopen(used.c_str(), "rb");
		if (fp) break;
	}
	if (!fp) { *err = "重みファイルが見つからない: " + path; return false; }

	EvalWeightsCore w{};                            // 途中で失敗しても *this を壊さないよう一時オブジェクトに読む
	bool seen[2][4][8] = {};                        // 既存 7 キー + core
	int  cur_side = -1, cur_bucket = -1;
	int  version = 1;                               // version 行が無いファイルは既存どおり 1 として扱う
	int  lineno = 0;
	string line;

	auto fail = [&](const string& why)
	{
		*err = used + ":" + to_string(lineno) + ": " + why;
		fclose(fp);
		return false;
	};

	while (evalw::read_line(fp, line))
	{
		lineno++;
		const size_t h = line.find('#');
		if (h != string::npos) line.erase(h);
		line = evalw::trim(line);
		if (line.empty()) continue;

		if (line[0] == '[')                             // --- セクション行 ---
		{
			if (line.back() != ']') return fail("セクションが ] で閉じていない: " + line);
			const string body = evalw::trim(line.substr(1, line.size() - 2));
			const size_t dot = body.find('.');
			if (dot == string::npos) return fail("セクション名が side.bucketN の形式でない: " + body);
			const string s = body.substr(0, dot), b = body.substr(dot + 1);
			if      (s == "fir") cur_side = 0;
			else if (s == "sec") cur_side = 1;
			else return fail("未知の side(fir / sec のみ): " + s);
			if (b.size() != 7 || b.compare(0, 6, "bucket") != 0 || b[6] < '0' || b[6] > '3')
				return fail("未知のバケット(bucket0..bucket3 のみ): " + b);
			cur_bucket = b[6] - '0';
			continue;
		}

		const size_t eq = line.find('=');
		if (eq == string::npos)                         // --- メタ情報行(key: value)---
		{
			const size_t co = line.find(':');
			if (co == string::npos) return fail("解釈できない行: " + line);
			const string k = evalw::trim(line.substr(0, co));
			const string v = evalw::trim(line.substr(co + 1));
			if (k == "version")
			{
				if      (v == "1") version = 1;
				else if (v == "2") version = 2;
				else return fail("未知の version: " + v);
			}
			else if (k == "name") w.base.name = v;
			else return fail("未知のメタ情報キー: " + k);
			continue;
		}

		// --- 配列行(key = v1,v2,...)---
		if (cur_side < 0) return fail("セクション [side.bucketN] より前に値行がある");
		const string k = evalw::trim(line.substr(0, eq));
		int ki = -1;
		for (int i = 0; i < 7; i++) if (k == evalw::KEY[i]) { ki = i; break; }
		if (k == evalwc::CORE_KEY) ki = evalwc::KEY_CORE;
		if (ki < 0) return fail("未知のキー: " + k);
		if (seen[cur_side][cur_bucket][ki]) return fail("キーが重複している: " + k);

		vector<int> v;
		string why;
		if (!evalw::parse_ints(line.substr(eq + 1), v, &why)) return fail(k + ": " + why);
		const int need = (ki == evalwc::KEY_CORE) ? core_feat::NUM : evalw::KLEN[ki];
		if ((int)v.size() != need)
			return fail(k + ": 要素数が " + to_string(need) + " ではなく " + to_string(v.size()));
		if (ki == 0 && (v[0] != 0 || v[3] != 0 || v[6] != 0))
			return fail("stdweight の index 0/3/6 は構造上 0 固定でなければならない");

		if (ki == evalwc::KEY_CORE)
		{
			int* const dst = (cur_side == 0 ? w.core_fir : w.core_sec) + cur_bucket * core_feat::NUM;
			for (int i = 0; i < core_feat::NUM; i++) dst[i] = v[i];
		}
		else
		{
			evalw::store(cur_side == 0 ? w.base.fir : w.base.sec, ki, cur_bucket, v);
		}
		seen[cur_side][cur_bucket][ki] = true;
	}
	fclose(fp);

	// 既存 7 キーは 32 セクションすべてに必須。core は version 2 なら必須、version 1 なら禁止。
	for (int s = 0; s < 2; s++) for (int b = 0; b < 4; b++)
	{
		const string sec_name = string("[") + (s == 0 ? "fir" : "sec") + ".bucket" + to_string(b) + "]";
		for (int i = 0; i < 7; i++)
			if (!seen[s][b][i]) { *err = used + ": " + sec_name + " の " + evalw::KEY[i] + " が無い"; return false; }
		if (version == 2 && !seen[s][b][evalwc::KEY_CORE])
		{
			*err = used + ": " + sec_name + " の core が無い(version: 2 では必須)";
			return false;
		}
		if (version == 1 && seen[s][b][evalwc::KEY_CORE])
		{
			*err = used + ": " + sec_name + " に core があるが version: 1 である(version: 2 にすること)";
			return false;
		}
	}

	w.base.build_tables();
	*this = w;
	return true;
}

// 重みを version 2 形式で出力する(検証・変換用)。
// 行整形は dump_eval_weights()(eval_weights.hpp:279-301)と同一で、各セクション末尾に core 行を足す。
inline void dump_eval_weights_core(ostream& os, const EvalWeightsCore& W)
{
	os << "# 立体四目並べ 評価関数重み(核 2 マスの全状態 core 付き)\n";
	os << "version: 2\n";
	os << "name: " << (W.base.name.empty() ? string("unnamed") : W.base.name) << "\n";
	for (int s = 0; s < 2; s++)
	{
		const SideWeights& S = (s == 0) ? W.base.fir : W.base.sec;
		const int* const C = (s == 0) ? W.core_fir : W.core_sec;
		for (int b = 0; b < 4; b++)
		{
			os << "\n[" << (s == 0 ? "fir" : "sec") << ".bucket" << b << "]\n";
			for (int i = 0; i <= 7; i++)
			{
				string k = (i < 7) ? evalw::KEY[i] : evalwc::CORE_KEY;
				k.resize(17, ' ');
				os << k << " = ";
				vector<int> v;
				if (i < 7) v = evalw::fetch(S, i, b);
				else       v.assign(C + b * core_feat::NUM, C + (b + 1) * core_feat::NUM);
				for (size_t j = 0; j < v.size(); j++) { if (j) os << ","; os << v[j]; }
				os << "\n";
			}
		}
	}
}

inline const EvalWeightsCore& EvalWeightsCore::builtin()
{
	static const EvalWeightsCore W = []()
	{
		EvalWeightsCore w{};                      // core_fir / core_sec は 0
		w.base = EvalWeights::builtin();
		return w;
	}();
	return W;
}
