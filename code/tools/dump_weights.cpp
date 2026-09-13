// 組み込み既定値 EvalWeights::builtin() を重みファイル形式で出力するツール。
// 設計: docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md §2.5 / §5.3
//
// weights/alpha/ver7_2.txt は「このツールの出力を保存したもの」とし、手打ちしない。
// これにより builtin() とファイルの二重管理を避ける。
//
//   g++ -std=c++17 -O2 code/tools/dump_weights.cpp -o dump_weights
//   ./dump_weights > weights/alpha/ver7_2.txt      # 生成
//   ./dump_weights --selfcheck               # 出力 → 再 load → builtin() と 256 値照合
//   ./dump_weights --check weights/alpha/ver7_2.txt # 既存ファイルが builtin() と一致するか照合

#include "../common.hpp"
#include "../eval_weights.hpp"

#include <cstdio>

static int selfcheck(const string& tmp_path)
{
	{
		ofstream ofs(tmp_path);
		if(!ofs) { cerr << "一時ファイルを作れない: " << tmp_path << endl; return 1; }
		dump_eval_weights(ofs, EvalWeights::builtin());
	}
	EvalWeights w;
	string err;
	const bool ok = w.load(tmp_path, &err);
	remove(tmp_path.c_str());
	if(!ok) { cerr << "NG: 書き出した内容を読み戻せない: " << err << endl; return 1; }
	if(!same_eval_weights(w, EvalWeights::builtin()))
	{
		cerr << "NG: 読み戻した重みが builtin() と一致しない" << endl;
		return 1;
	}
	cout << "OK: dump → load → builtin() の 256 値が完全一致 (name=" << w.name << ")" << endl;
	return 0;
}

static int check_file(const string& path)
{
	EvalWeights w;
	string err;
	if(!w.load(path, &err)) { cerr << "NG: " << err << endl; return 1; }
	if(!same_eval_weights(w, EvalWeights::builtin()))
	{
		cerr << "NG: " << path << " の重みが builtin() と一致しない" << endl;
		return 1;
	}
	cout << "OK: " << path << " の 256 値が builtin() と完全一致 (name=" << w.name << ")" << endl;
	return 0;
}

int main(int argc, char** argv)
{
	const string mode = argc > 1 ? argv[1] : "";
	if(mode == "--selfcheck") return selfcheck(".dump_weights_selfcheck.tmp");
	if(mode == "--check")
	{
		if(argc < 3) { cerr << "usage: dump_weights --check <path>" << endl; return 2; }
		return check_file(argv[2]);
	}
	if(!mode.empty()) { cerr << "usage: dump_weights [--selfcheck | --check <path>]" << endl; return 2; }

	dump_eval_weights(cout, EvalWeights::builtin());
	return 0;
}
