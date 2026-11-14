// 新パラメータ候補の事前調査用ダンプツール(調査専用。学習・対局コードには一切触れない)
//
// 目的: 「現行 29 パラメータの特徴量」+「盤面ビットボード」+「教師値」+「最終結果」を
//       1 局面 1 レコードのバイナリで吐き、候補特徴量の評価を numpy 側で自由に行えるようにする。
//
// 特徴量 29 本の作り方は MachineLearning/main_gd_both.cpp:443-468 と同一
// (ps[p]=1 の単位ベクトルで evaluate_feature を叩いて出現数を取る線形性を利用)。
// 定数項 A[..][pnum] は turn<60 では 0 になるので保存しない(assert で確認する)。
//
// 出力: MachineLearning/tools/out/probe_ver8_2.bin  (little endian, packed)
// ビルド: g++ -O2 -std=c++17 -o probe_features.exe probe_features.cpp

#include "../../code/common.hpp"
#include "../../code/board.hpp"
#include "../evaluate_gd_both.hpp"

static const char *INPUT_FIRST_EVALUATE  = "/yonmoku/teacher/first_evaluate_ver8_2.csv";
static const char *INPUT_SECOND_EVALUATE = "/yonmoku/teacher/second_evaluate_ver8_2.csv";
static const char *INPUT_RECORD          = "/yonmoku/teacher/record_ver8_2.csv";
static const int   gameNum               = 93600;
static const char *OUTPUT                = "out/probe_ver8_2.bin";

// ダンプする ply の範囲(= bucket0/bucket1 相当。序中盤の調査が目的)
static const int PLY_MIN = 3, PLY_MAX = 31;

static const int PNUM = 29;

static int record_[100001][65];
static int evfir[100001][34];
static int evsec[100001][34];

#pragma pack(push, 1)
struct Row
{
	unsigned long long Me, You;   // Me = 手番側
	int   game;                   // 1..gameNum(train/test 分割用)
	int   teacher;                // 教師値(相手側エンジンの評価値)
	short ply;                    // record 添字。turn = ply + 2
	signed char result;           // +1 黒勝ち / -1 白勝ち / 0 引き分け
	signed char side;             // 0 = fir(黒手番) / 1 = sec(白手番)
	short f[PNUM];                // 現行 29 パラメータの出現数
};
#pragma pack(pop)
static_assert(sizeof(Row) == 8+8+4+4+2+1+1+2*PNUM, "packed");

static void read_csv(const char *path, int (*dst)[34], int cols)
{
	ifstream ifs(path);
	if (!ifs) { cerr << "open failed: " << path << endl; exit(1); }
	string line;
	int t = 1;
	while (getline(ifs, line))
	{
		istringstream is(line);
		int v, i = 0;
		while (is >> v) { if (i < cols) dst[t][i] = v; i++; is.ignore(); }
		t++;
	}
	cerr << path << ": " << (t - 1) << " lines" << endl;
}

static void read_record(const char *path)
{
	ifstream ifs(path);
	if (!ifs) { cerr << "open failed: " << path << endl; exit(1); }
	string line;
	int t = 1;
	while (getline(ifs, line))
	{
		istringstream is(line);
		int v, i = 0;
		while (is >> v) { if (i < 65) record_[t][i] = v; i++; is.ignore(); }
		t++;
	}
	cerr << path << ": " << (t - 1) << " lines" << endl;
}

int main()
{
	init_lines();
	read_record(INPUT_RECORD);
	{   // evaluate csv は [34] 幅
		static int tmp[100001][34];
		(void)tmp;
	}
	read_csv(INPUT_FIRST_EVALUATE,  evfir, 34);
	read_csv(INPUT_SECOND_EVALUATE, evsec, 34);

	FILE *fp = fopen(OUTPUT, "wb");
	if (!fp) { cerr << "cannot open output " << OUTPUT << endl; return 1; }

	long long rows = 0;
	vector<Row> buf;
	buf.reserve(1 << 16);

	for (int n = 1; n <= gameNum; n++)
	{
		// --- 1 パス目: 最後まで再生して勝敗を求める ---
		int result = 0;
		{
			Board c;
			for (int i = 0; i < 64 && record_[n][i] < INF; i++)
			{
				const int x = record_[n][i] % 4, y = 3 - (record_[n][i] / 4);
				if (c.place(x, y) == State::End)
				{
					// 直前に置いたのは turn = i+1 の手番 = (i 偶数なら黒 / 奇数なら白)
					result = (i % 2 == 0) ? +1 : -1;
					break;
				}
			}
		}

		// --- 2 パス目: 指定 ply の局面を書き出す ---
		Board c;
		for (int i = 0; i < 64; i++)
		{
			if (record_[n][i] >= INF) break;
			const int x = record_[n][i] % 4, y = 3 - (record_[n][i] / 4);
			if (c.place(x, y) == State::Invalid) { cerr << "invalid move g=" << n << " i=" << i << endl; return 1; }
			if (i < PLY_MIN || i > PLY_MAX) continue;

			const int teacher = (i % 2 == 1) ? evsec[n][i / 2] : evfir[n][i / 2];
			if (!(teacher > -INF && teacher < INF)) continue;

			Row r{};
			r.Me = c.Me; r.You = c.You;
			r.game = n; r.teacher = teacher;
			r.ply = (short)i; r.result = (signed char)result;
			r.side = (signed char)((i % 2 == 1) ? 0 : 1);

			int ps[PNUM];
			for (int p = 0; p <= PNUM; p++)
			{
				for (int k = 0; k < PNUM; k++) ps[k] = 0;
				if (p < PNUM) ps[p] = 1;
				gd::set_parameters(ps);
				const int v = gd::evaluate_feature(c);
				if (p == PNUM) { if (v != 0) { cerr << "nonzero const term at g=" << n << " i=" << i << ": " << v << endl; return 1; } }
				else r.f[p] = (short)v;
			}
			buf.push_back(r);
			rows++;
		}
		if (buf.size() >= (1u << 15)) { fwrite(buf.data(), sizeof(Row), buf.size(), fp); buf.clear(); }
		if (n % 10000 == 0) cerr << "game " << n << " rows=" << rows << endl;
	}
	if (!buf.empty()) fwrite(buf.data(), sizeof(Row), buf.size(), fp);
	fclose(fp);
	cerr << "wrote " << rows << " rows, " << sizeof(Row) << " B/row -> " << OUTPUT << endl;
	return 0;
}
