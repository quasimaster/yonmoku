// gd_weights_out.hpp の出力が weights/verX_Y.txt としてそのまま通用することを確かめる。
//
//   1. gdout::dump_weights_file() で適当な重みを書き出す
//   2. それを本番のパーサ code/eval_weights.hpp の EvalWeights::load() で読む
//   3. 本番の dump_eval_weights() で書き戻す
//   4. 1 と 3 の文字列が完全一致することを確認する
//
// これが通れば「出力をコピペするだけで重みファイルになる」ことが保証される
// (書式が 1 文字でも違えば load が失敗するか、書き戻しと差が出る)。
//
// ビルド:
//   g++ -std=c++17 -O2 -o verify_weights_format.exe MachineLearning/tools/verify_weights_format.cpp

#include "../../code/common.hpp"
#include "../../code/eval_weights.hpp"
#include "../gd_weights_out.hpp"
#include "../console_utf8.hpp"

int main()
{
	//コンソールの出力コードページを UTF-8 に合わせる(日本語の文字化け対策)
	enable_utf8_console();
	int fir[4][29], sec[4][29];
	mt19937 r(20260906u);
	uniform_int_distribution<int> dist(-2000, 2000);
	for (int b = 0; b < 4; b++)
		for (int i = 0; i < 29; i++) { fir[b][i] = dist(r); sec[b][i] = dist(r); }

	ostringstream mine;
	gdout::dump_weights_file(mine, "verTEST", fir, sec);

	const string tmp = "verify_weights_format.tmp.txt";
	{
		ofstream ofs(tmp, ios::binary);
		if (!ofs) { cout << "NG: 一時ファイルを開けない" << endl; return 1; }
		ofs << mine.str();
	}

	EvalWeights W;
	string err;
	if (!W.load(tmp, &err))
	{
		cout << "NG: 本番パーサが読めなかった: " << err << endl;
		remove(tmp.c_str());
		return 1;
	}

	ostringstream official;
	dump_eval_weights(official, W);
	remove(tmp.c_str());

	if (mine.str() != official.str())
	{
		cout << "NG: 書式が dump_eval_weights と一致しない" << endl;
		// 最初に違う行を出す
		istringstream a(mine.str()), b(official.str());
		string la, lb;
		int ln = 1;
		while (true)
		{
			const bool ga = (bool)getline(a, la);
			const bool gb = (bool)getline(b, lb);
			if (!ga && !gb) break;
			if (!ga) la = "<EOF>";
			if (!gb) lb = "<EOF>";
			if (la != lb)
			{
				cout << "  line " << ln << endl;
				cout << "    mine     : [" << la << "]" << endl;
				cout << "    official : [" << lb << "]" << endl;
				break;
			}
			ln++;
		}
		return 1;
	}

	// 値そのものの対応(添字マッピング)も確認する
	int bad = 0;
	for (int s = 0; s < 2; s++)
	{
		const SideWeights &S = (s == 0) ? W.fir : W.sec;
		const int (*w)[29] = (s == 0) ? fir : sec;
		for (int b = 0; b < 4; b++)
		{
			const int *v = w[b];
			const int expect_std[7] = {0, v[0], v[1], 0, v[2], v[3], 0};
			for (int i = 0; i < 7; i++) if (S.stdweight[b * 7 + i] != expect_std[i]) bad++;
			for (int i = 0; i < 8; i++) if (S.maketweight[b * 8 + i] != v[15 + i]) bad++;
			for (int i = 0; i < 6; i++) if (S.conti_maketweight[b * 6 + i] != v[23 + i]) bad++;
			for (int i = 0; i < 3; i++) if (S.layer_inter[b * 10 + 0 + i] != v[4 + i]) bad++;
			for (int i = 0; i < 3; i++) if (S.layer_inter[b * 10 + 3 + i] != v[7 + i]) bad++;
			for (int i = 0; i < 4; i++) if (S.layer_inter[b * 10 + 6 + i] != v[10 + i]) bad++;
			if (S.continuous[b] != v[14]) bad++;
		}
	}
	if (bad) { cout << "NG: 添字の対応が " << bad << " 箇所ずれている" << endl; return 1; }

	// loss コメントを足しても本番パーサの読み取り結果が変わらないことを確かめる。
	// (code/eval_weights.hpp:209-210 が # 以降を捨てるので、値は同じになるはず)
	{
		long double firLoss[4] = {12345.678L, 98765.4321L, 1.5L, (long double)INF};// 末尾は「改善なし」表示になる
		long double secLoss[4] = {23456.789L, 34567.891L, 45678.912L, 56789.123L};

		ostringstream withloss;
		gdout::dump_weights_file(withloss, "verTEST", fir, sec, firLoss, secLoss);

		const string tmp2 = "verify_weights_format.loss.tmp.txt";
		{
			ofstream ofs(tmp2, ios::binary);
			if (!ofs) { cout << "NG: 一時ファイル(loss 付き)を開けない" << endl; return 1; }
			ofs << withloss.str();
		}

		EvalWeights W2;
		string err2;
		if (!W2.load(tmp2, &err2))
		{
			cout << "NG: loss コメント付きを本番パーサが読めなかった: " << err2 << endl;
			remove(tmp2.c_str());
			return 1;
		}
		remove(tmp2.c_str());

		ostringstream official2;
		dump_eval_weights(official2, W2);
		if (official2.str() != official.str())
		{
			cout << "NG: loss コメントの有無で読み込み結果が変わった" << endl;
			return 1;
		}
		cout << "OK: loss コメントを足しても読み込み結果は変わらない" << endl;
	}
	cout << "name = " << W.name << endl;
	cout << "OK: 出力は本番パーサで読め、dump_eval_weights と完全一致、添字対応も 256 個すべて一致" << endl;
	return 0;
}
