#pragma once

#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <cerrno>

#include "common.hpp"

// 評価関数の重み(1 モデル = 先手用 + 後手用)を保持する構造体と、そのテキスト入出力。
// 設計: docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md
//
// 添字規約は現行の evaluate_alpha_inc_tbl.hpp / evaluate_alpha_t.hpp の配列と完全に同一。
// 重み値そのものは builtin() が現行のリテラルを保持するので、
// 組み込み既定値を使う限り既存実装と 1 ノードも変わらない。
//
// ★環境依存の注意(本環境で実測して判明):
//   MinGW-w64 g++ 13.2.0 + 共有 libstdc++ では、ヘッダ内の inline 関数の中で
//   std::ifstream / std::istringstream を「構築」すると -O1 以上で SEGV する
//   (libstdc++ DLL の vtable を auto-import する疑似再配置が COMDAT セクションで壊れる)。
//   最小再現は inline 関数内の `std::ifstream ifs; ifs.open(p);` だけ。
//   .cpp 内の static 関数(既存の load_openings 等)は影響を受けない。
//   そのため本ヘッダのファイル入力は cstdio(FILE*)で行う。
//   構築済みの ostream& を受け取って書くだけの dump_eval_weights は該当しない。

// ===== 片側(先手用 / 後手用)の重み =====
struct SideWeights
{
	int stdweight[28];          // [bucket*7 + v+3]   ※ index 0,3,6 は構造上 0 固定
	int maketweight[32];        // [bucket*8 + k]     k=0..3 Me / 4..7 You
	int conti_maketweight[24];  // [bucket*6 + k]     k=0..2 Me(T_T,T_W,W_T) / 3..5 You
	int continuous[4];          // [bucket]           continuous_{fir,sec}_t の parameter
	int layer_inter[40];        // [bucket*10 + k]    0..2 layer_me / 3..5 layer_you / 6..9 intersection
};

// ===== 1 モデル = 先手用 + 後手用 の一式 =====
// reach_layer_intersection_t が手番に応じて fir/sec を両方参照するため、
// 重みの受け渡し単位は必ず「モデル全体」でなければならない(設計書 §2.1)。
struct EvalWeights
{
	string       name;          // "ver7.2" 等。ログ表示・実験記録用
	SideWeights  fir, sec;

	// 現行 init_cnt_tbl() が作るグローバル表を、モデルごとの実体に移したもの
	alignas(64) int stdweight_fir_tbl[4][256];
	alignas(64) int stdweight_sec_tbl[4][256];

	void build_tables();                            // init_cnt_tbl() の stdweight 部をそのまま移植
	bool load(const string& path, string* err);     // テキスト読込 → build_tables()
	static const EvalWeights& builtin();            // 組み込み既定値(= 現行の数値)
};

// flag_tbl は重みに依存しないのでグローバルのまま据え置く(現行 evaluate_alpha_inc_tbl.hpp:17)
alignas(64) inline unsigned char flag_tbl[256];

// idx = (count_me << 4 | count_you) から v を求める規約。build_tables / init_flag_tbl で共有する。
inline int eval_cnt_to_v(int idx)
{
	const int cme = idx >> 4, cyou = idx & 15;
	return (cme && cyou) ? 0 : (cme ? cme : -cyou);   // board.count() と同じ規約(両者混在は 0)
}

inline void init_flag_tbl()
{
	for (int idx = 0; idx < 256; idx++)
	{
		const int v = eval_cnt_to_v(idx);
		flag_tbl[idx] = (unsigned char)((v == 2 ? 1 : 0) | (v == -2 ? 2 : 0));
	}
}

// 現行 init_cnt_tbl()(evaluate_alpha_inc_tbl.hpp:34-47)の stdweight 部と同一。
inline void EvalWeights::build_tables()
{
	for (int idx = 0; idx < 256; idx++)
	{
		const int v = eval_cnt_to_v(idx);
		// |v| == 4 は勝敗確定済みラインで評価中には現れないが、テーブルは全 idx を埋めるため
		// ±3 に丸めて構築する(stdweight の両端は 0 なので値も一致する)
		const int vc = max(-3, min(3, v));
		for (int b = 0; b < 4; b++)
		{
			stdweight_fir_tbl[b][idx] = fir.stdweight[b * 7 + vc + 3];
			stdweight_sec_tbl[b][idx] = sec.stdweight[b * 7 + vc + 3];
		}
	}
}

// ===== テキスト形式の読み書き(設計書 §2.4)=====
namespace evalw
{
	// セクションごとのキー定義。順序は設計書の表と同じ。
	inline const char* const KEY[7]  = {"stdweight", "maketweight", "conti_maketweight",
	                                    "layer_me", "layer_you", "intersection", "continuous"};
	inline const int         KLEN[7] = {7, 8, 6, 3, 3, 4, 1};

	inline string trim(const string& s)
	{
		const size_t a = s.find_first_not_of(" \t\r\n");
		if (a == string::npos) return "";
		const size_t b = s.find_last_not_of(" \t\r\n");
		return s.substr(a, b - a + 1);
	}

	// FILE* から 1 行読む(改行は含めない)。EOF で 1 文字も読めなければ false。
	// ※ ヘッダ inline 内で std::ifstream を構築できないための代替(冒頭の注意を参照)。
	inline bool read_line(FILE* fp, string& out)
	{
		out.clear();
		int c;
		bool any = false;
		while ((c = fgetc(fp)) != EOF)
		{
			any = true;
			if (c == '\n') return true;
			out.push_back((char)c);
		}
		return any;
	}

	// "1,-2, 3" → {1,-2,3}。数値以外・空要素があれば false(理由を why に入れる)。
	inline bool parse_ints(const string& s, vector<int>& out, string* why)
	{
		out.clear();
		size_t i = 0;
		while (true)
		{
			const size_t c = s.find(',', i);
			const string t = trim(c == string::npos ? s.substr(i) : s.substr(i, c - i));
			if (t.empty()) { *why = "空の要素がある"; return false; }
			errno = 0;
			char* end = nullptr;
			const long v = strtol(t.c_str(), &end, 10);
			if (end != t.c_str() + t.size()) { *why = "数値として読めない: \"" + t + "\""; return false; }
			if (errno == ERANGE || v < INT_MIN || v > INT_MAX) { *why = "int の範囲外: \"" + t + "\""; return false; }
			out.push_back((int)v);
			if (c == string::npos) break;
			i = c + 1;
		}
		return !out.empty();
	}

	// 1 セクション分の値を SideWeights の該当バケットへ書き込む。
	inline void store(SideWeights& S, int key, int bucket, const vector<int>& v)
	{
		switch (key)
		{
			case 0: for (int i = 0; i < 7; i++) S.stdweight[bucket * 7 + i]         = v[i]; break;
			case 1: for (int i = 0; i < 8; i++) S.maketweight[bucket * 8 + i]       = v[i]; break;
			case 2: for (int i = 0; i < 6; i++) S.conti_maketweight[bucket * 6 + i] = v[i]; break;
			case 3: for (int i = 0; i < 3; i++) S.layer_inter[bucket * 10 + 0 + i]  = v[i]; break;
			case 4: for (int i = 0; i < 3; i++) S.layer_inter[bucket * 10 + 3 + i]  = v[i]; break;
			case 5: for (int i = 0; i < 4; i++) S.layer_inter[bucket * 10 + 6 + i]  = v[i]; break;
			case 6: S.continuous[bucket] = v[0]; break;
		}
	}

	// 1 セクション分の値を SideWeights から取り出す(dump 用。store の逆)。
	inline vector<int> fetch(const SideWeights& S, int key, int bucket)
	{
		vector<int> v;
		switch (key)
		{
			case 0: for (int i = 0; i < 7; i++) v.push_back(S.stdweight[bucket * 7 + i]);         break;
			case 1: for (int i = 0; i < 8; i++) v.push_back(S.maketweight[bucket * 8 + i]);       break;
			case 2: for (int i = 0; i < 6; i++) v.push_back(S.conti_maketweight[bucket * 6 + i]); break;
			case 3: for (int i = 0; i < 3; i++) v.push_back(S.layer_inter[bucket * 10 + 0 + i]);  break;
			case 4: for (int i = 0; i < 3; i++) v.push_back(S.layer_inter[bucket * 10 + 3 + i]);  break;
			case 5: for (int i = 0; i < 4; i++) v.push_back(S.layer_inter[bucket * 10 + 6 + i]);  break;
			case 6: v.push_back(S.continuous[bucket]); break;
		}
		return v;
	}
}

// 重みファイルを読み込む。失敗時は false を返し err に「パス:行番号: 理由」を入れる。
// ★組み込み既定値への暗黙フォールバックはしない(設計書 §2.4)。呼び出し側で必ず終了すること。
inline bool EvalWeights::load(const string& path, string* err)
{
	// 実行ディレクトリ依存を吸収する(load_openings と同じプレフィックス探索)
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

	bool seen[2][4][7] = {};
	int  cur_side = -1, cur_bucket = -1;
	int  lineno = 0;
	string line;
	name.clear();

	// エラー時の共通処理(パス:行番号: 理由 を組み立ててファイルを閉じる)
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
		if (h != string::npos) line.erase(h);          // # 以降は行末までコメント
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
			if      (k == "version") { if (v != "1") return fail("未知の version: " + v); }
			else if (k == "name")    name = v;
			else return fail("未知のメタ情報キー: " + k);
			continue;
		}

		// --- 配列行(key = v1,v2,...)---
		if (cur_side < 0) return fail("セクション [side.bucketN] より前に値行がある");
		const string k = evalw::trim(line.substr(0, eq));
		int ki = -1;
		for (int i = 0; i < 7; i++) if (k == evalw::KEY[i]) { ki = i; break; }
		if (ki < 0) return fail("未知のキー: " + k);
		if (seen[cur_side][cur_bucket][ki]) return fail("キーが重複している: " + k);

		vector<int> v;
		string why;
		if (!evalw::parse_ints(line.substr(eq + 1), v, &why)) return fail(k + ": " + why);
		if ((int)v.size() != evalw::KLEN[ki])
			return fail(k + ": 要素数が " + to_string(evalw::KLEN[ki]) + " ではなく " + to_string(v.size()));
		if (ki == 0 && (v[0] != 0 || v[3] != 0 || v[6] != 0))
			return fail("stdweight の index 0/3/6 は構造上 0 固定でなければならない");

		evalw::store(cur_side == 0 ? fir : sec, ki, cur_bucket, v);
		seen[cur_side][cur_bucket][ki] = true;
	}
	fclose(fp);

	// 32 セクション × 7 キーが全て揃っているか
	for (int s = 0; s < 2; s++) for (int b = 0; b < 4; b++) for (int i = 0; i < 7; i++)
		if (!seen[s][b][i])
		{
			*err = used + ": [" + (s == 0 ? "fir" : "sec") + ".bucket" + to_string(b)
			     + "] の " + evalw::KEY[i] + " が無い";
			return false;
		}

	build_tables();
	return true;
}

// 重みを §2.4 の形式で出力する(dump_weights / 検証用)。
// ※ ostream は「受け取るだけ」なので冒頭の環境依存の注意には該当しない。
inline void dump_eval_weights(ostream& os, const EvalWeights& W)
{
	os << "# 立体四目並べ 評価関数重み\n";
	os << "version: 1\n";
	os << "name: " << (W.name.empty() ? string("unnamed") : W.name) << "\n";
	for (int s = 0; s < 2; s++)
	{
		const SideWeights& S = (s == 0) ? W.fir : W.sec;
		for (int b = 0; b < 4; b++)
		{
			os << "\n[" << (s == 0 ? "fir" : "sec") << ".bucket" << b << "]\n";
			for (int i = 0; i < 7; i++)
			{
				string k = evalw::KEY[i];
				k.resize(17, ' ');                       // 桁揃え(conti_maketweight が最長 17 文字)
				os << k << " = ";
				const vector<int> v = evalw::fetch(S, i, b);
				for (size_t j = 0; j < v.size(); j++) { if (j) os << ","; os << v[j]; }
				os << "\n";
			}
		}
	}
}

// ===== 組み込み既定値 =====
// 数値は evaluate_alpha_inc_tbl.hpp:22,28,58,65,133,140 および
// evaluate_alpha_t.hpp:32,42,94,100 からそのまま転記したもの(ver7.2 相当)。
inline const EvalWeights& EvalWeights::builtin()
{
	static const EvalWeights W = []()
	{
		EvalWeights w{};
		w.name = "ver7.2";

		// --- evaluate_alpha_inc_tbl.hpp:22 stdweight_fir ---
		const int stdweight_fir[28] = {
			0,-61,-22,0,28,65,0,
			0,-84,-23,0,29,103,0,
			0,-77,-8,0,18,63,0,
			0,-79,-27,0,-19,18,0
		};
		// --- evaluate_alpha_inc_tbl.hpp:28 stdweight_sec ---
		const int stdweight_sec[28] = {
			0,-46,-19,0,23,61,0,
			0,-77,-20,0,27,111,0,
			0,-36,7,0,22,92,0,
			0,2,21,0,26,118,0
		};
		// --- evaluate_alpha_inc_tbl.hpp:58 maketweight (evaluate_pointfir_it) ---
		const int maketweight_fir[32] = {
			53,-13,50,4,22,-50,27,16,
			145,-75,77,24,40,-54,44,30,
			320,-61,114,66,110,-12,55,45,
			578,-213,143,138,256,6,25,30
		};
		// --- evaluate_alpha_inc_tbl.hpp:133 maketweight (evaluate_pointsec_it) ---
		const int maketweight_sec[32] = {
			9,-62,27,4,89,-11,41,13,
			44,-52,38,15,119,-93,69,36,
			77,-23,58,35,290,-71,113,77,
			286,-46,12,1,549,-235,125,132
		};
		// --- evaluate_alpha_inc_tbl.hpp:65 conti_maketweight (fir) ---
		const int conti_fir[24] = {
			215,189,284,86,160,154,
			236,317,92,77,119,83,
			337,638,141,145,286,35,
			689,1166,173,363,505,-80
		};
		// --- evaluate_alpha_inc_tbl.hpp:140 conti_maketweight (sec) ---
		const int conti_sec[24] = {
			108,112,30,171,135,220,
			84,120,30,209,246,125,
			133,270,11,381,667,180,
			269,363,-245,757,1329,311
		};
		// --- evaluate_alpha_t.hpp:32 continuous_fir_t parameter ---
		const int continuous_fir[4] = {3108,1070,674,671};
		// --- evaluate_alpha_t.hpp:42 continuous_sec_t parameter ---
		const int continuous_sec[4] = {1308,1131,744,698};
		// --- evaluate_alpha_t.hpp:94 weightfir ---
		const int weightfir[40] = {
			138,476,144,215,209,192,149,-1104,-29,1327,
			177,624,171,314,397,266,341,272,1062,966,
			149,859,124,327,613,258,489,376,567,966,
			164,1467,136,449,985,321,1089,627,1698,-80
		};
		// --- evaluate_alpha_t.hpp:100 weightsec ---
		const int weightsec[40] = {
			231,232,210,151,455,158,345,865,-187,189,
			321,431,284,197,599,180,291,361,152,132,
			298,677,249,175,871,131,509,357,790,1294,
			506,1288,373,158,1361,91,1058,902,2057,672
		};

		memcpy(w.fir.stdweight,         stdweight_fir,   sizeof(stdweight_fir));
		memcpy(w.sec.stdweight,         stdweight_sec,   sizeof(stdweight_sec));
		memcpy(w.fir.maketweight,       maketweight_fir, sizeof(maketweight_fir));
		memcpy(w.sec.maketweight,       maketweight_sec, sizeof(maketweight_sec));
		memcpy(w.fir.conti_maketweight, conti_fir,       sizeof(conti_fir));
		memcpy(w.sec.conti_maketweight, conti_sec,       sizeof(conti_sec));
		memcpy(w.fir.continuous,        continuous_fir,  sizeof(continuous_fir));
		memcpy(w.sec.continuous,        continuous_sec,  sizeof(continuous_sec));
		memcpy(w.fir.layer_inter,       weightfir,       sizeof(weightfir));
		memcpy(w.sec.layer_inter,       weightsec,       sizeof(weightsec));

		w.build_tables();
		return w;
	}();
	return W;
}

// 2 モデルの生の重み 256 値が完全一致するか(検証用。派生表は build_tables で決まるので見ない)
inline bool same_eval_weights(const EvalWeights& a, const EvalWeights& b)
{
	return memcmp(&a.fir, &b.fir, sizeof(SideWeights)) == 0
	    && memcmp(&a.sec, &b.sec, sizeof(SideWeights)) == 0;
}
