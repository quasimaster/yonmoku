// yonmoku_gradient_descent_bonanza_first.cpp の高速・省メモリ版。
// 学習対象は code/yonmoku_Bonanza_2line.cpp の bonanza_2line(2 ライン組の全状態表)。
//
// ビルド(-static は MinGW の DLL 取り違え対策。-march=native で AVX2 の gather を使う):
//   g++ -O2 -march=native -fopenmp -static -o yonmoku_gradient_descent_bonanza_fast.exe yonmoku_gradient_descent_bonanza_fast.cpp
//
// 使い方(引数なしなら元コードと同じ ver7_1 を全試合読み、同じ場所へ出力する):
//   yonmoku_gradient_descent_bonanza_fast.exe [オプション]
//     -d <record.csv> <second_evaluate.csv>  教師データの組。複数回指定可(スレッド別ファイルをまとめて読める)
//     -g <N>        読む試合数の上限(既定: 全部。元コードは 500 固定)
//     -o <path>     出力先(既定: /yonmoku/feature/feature.csv)
//     -j <N>        スレッド数(既定: 全論理コア)
//     -t <N>        外側の再試行回数(既定 50。元コードと同じ)
//     -n <N>        内側の反復回数(既定 1000。元コードと同じ)
//     -s <seed>     乱数シード(既定: random_device。元コードと同じく毎回変わる)
//     --verify <N>  先頭 N 試合で検算して終了(評価値が bonanza_2line と一致するか、
//                   loss と勾配が「局面ごとに素直に計算した値」と一致するか)
//
// ===== 元コードからの変更点 =====
// 勾配降下法の本体(符号ステップ + 連続回数ぶんの加速 + 閾値 1.05^n + L1 正則化 + 収束判定 +
// 再試行)と、教師値・予測値の変換式(±1840 で 0.01/0.99 に丸める / 400 で割るシグモイド)、
// 対象局面(record 添字が奇数 = 黒番の局面、評価値が ±INF でないもの)は元コードと同一。
//
// [メモリ]
//   元: evaluatesfir/evaluatessec/record を 10 万試合ぶんの固定長 int 配列で持つ(10 万試合が上限)。
//   新: 学習局面を「盤面(黒, 白) + 教師値の和 + 出現回数」の 32 byte で持ち、同一盤面は 1 つにまとめる。
//       ver7_1(65536 試合)で 106 万局面 → 78 万局面、24 MB。10 万試合でおよそ 40〜50 MB。
//       CSV は 1 行ずつ読み、ファイル全体をメモリに置かない。first_evaluate は学習に使っていないので読まない。
//
// [速度]
//   1. 同一盤面の統合。出現回数 m・教師値の和 Σp を持てば
//        loss = -(Σp) log q - (m - Σp) log(1 - q),  勾配 = Σp - m q
//      で、局面を 1 つずつ数えた場合と数学的に同じ値になる(浮動小数の足す順序だけが違う)。
//   2. 特徴量(2850 組の状態)を反復ごとに 64 局面ぶん作り直していた処理を、学習に使う局面だけにした。
//   3. 局面をブロックにまとめ、重み・勾配へのアクセスを L1 に収まる範囲に閉じ込めた(下の「学習本体」)。
//      順伝播は AVX2 の gather で 8 局面ずつ。
//   4. OpenMP でブロック単位に並列化。勾配はスレッドごとのバッファに足して最後に合計する。
//   5. pow(1.05, n) を 18 万回 → 1 回/反復。exp/log は long double → double。
//
// [元コードの不具合の修正] ※学習結果が変わる。bonanza_2line(推論側)と一致させるための修正
//   (a) 学習ループで状態 27/63 の組を continue で飛ばすとき k++ も飛んでいた。k が進まないので
//       以降は同じ B[i][k](= 27/63)を読み続け、その局面で最初に 27/63 の組が出た時点から先の組は
//       すべて学習されていなかった(序盤ほど (0,1) 番目のような先頭の組がすぐ 空×空 になる)。
//   (b) cnt[] を「今置いたマスを通るライン」だけ再計算していたが、place() のたびに Me/You が
//       入れ替わるため、再計算されなかったラインは前の手番の視点(符号が逆)のまま残っていた。
//       推論側 board.count() は全ラインを現在の Me 視点で数える。
//       新コードは学習局面ごとに 76 本すべてを Me(= 黒)視点で数え直す。
//   (c) 状態 27/63 の重みは学習しないのに乱数初期値のまま出力されることがあった
//       (正則化で 1 ずつ 0 へ寄るだけなので、早く収束すると残る)。推論ではこの値も足されるため、
//       新コードでは常に 0 に固定する(元コードで十分反復した場合と同じ状態)。
//   (d) 勝ち手の直後の局面(4 つ揃ったライン = cnt -4)は重み表の外を指すので読み込み時に外す。
//       元コードでもこの局面の評価値は INF なので学習対象外であり、結果は変わらない。
//
// 出力書式は元コードと同一(1 行 = 1 組 64 個 + 末尾カンマ、2850 行)。

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <cassert>
#include <vector>
#include <string>
#include <random>
#include <chrono>
#include <algorithm>
#include <omp.h>
#ifdef __AVX2__
#include <immintrin.h>
#endif

#include "console_utf8.hpp"

using namespace std;

static const int SIZE = 4;
#define IDX(x, y, z) ((x) + (y) * SIZE + (z) * SIZE * SIZE)
#define BIT(x, y, z) (1uLL << IDX(x, y, z))
static const int INF = 1e9;
static const int LINES_NUM = 76;
static const int PAIRS = LINES_NUM * (LINES_NUM - 1) / 2;  // 2850
static const int PNUM = 64;                                 // (cnt[i]+3)*8 + (cnt[j]+3)
static const int NPARAM = PAIRS * PNUM;
static const int P_EMPTY = 27;                              // 空 × 空
static const int P_DEAD = 63;                               // 死 × 死

static unsigned long long LINES[LINES_NUM];
static int ROWBASE[LINES_NUM];  // 組 (l1, j) の重み添字 = ROWBASE[l1] + (cnt[l1]+3)*8 + j*64 + (cnt[j]+3)

static bool is_fixed_zero(int p) { return p == P_EMPTY || p == P_DEAD; }

// ---- ライン生成(元コードと同じ順序。重みの行番号 k がこの順に依存する) ----
static void init_lines()
{
	vector<unsigned long long> lines;
	for (int x = 0; x < SIZE; x++) for (int y = 0; y < SIZE; y++)
	{
		unsigned long long line = 0uLL;
		for (int z = 0; z < SIZE; z++) line |= BIT(x, y, z);
		lines.push_back(line);
	}
	for (int y = 0; y < SIZE; y++) for (int z = 0; z < SIZE; z++)
	{
		unsigned long long line = 0uLL;
		for (int x = 0; x < SIZE; x++) line |= BIT(x, y, z);
		lines.push_back(line);
	}
	for (int z = 0; z < SIZE; z++) for (int x = 0; x < SIZE; x++)
	{
		unsigned long long line = 0uLL;
		for (int y = 0; y < SIZE; y++) line |= BIT(x, y, z);
		lines.push_back(line);
	}
	for (int x = 0; x < SIZE; x++)
	{
		unsigned long long line1 = 0uLL, line2 = 0uLL;
		for (int yz = 0; yz < SIZE; yz++)
		{
			line1 |= BIT(x, yz, yz);
			line2 |= BIT(x, yz, SIZE - 1 - yz);
		}
		lines.push_back(line1);
		lines.push_back(line2);
	}
	for (int y = 0; y < SIZE; y++)
	{
		unsigned long long line1 = 0uLL, line2 = 0uLL;
		for (int zx = 0; zx < SIZE; zx++)
		{
			line1 |= BIT(zx, y, zx);
			line2 |= BIT(zx, y, SIZE - 1 - zx);
		}
		lines.push_back(line1);
		lines.push_back(line2);
	}
	for (int z = 0; z < SIZE; z++)
	{
		unsigned long long line1 = 0uLL, line2 = 0uLL;
		for (int xy = 0; xy < SIZE; xy++)
		{
			line1 |= BIT(xy, xy, z);
			line2 |= BIT(xy, SIZE - 1 - xy, z);
		}
		lines.push_back(line1);
		lines.push_back(line2);
	}
	{
		unsigned long long line1 = 0uLL, line2 = 0uLL, line3 = 0uLL, line4 = 0uLL;
		for (int xyz = 0; xyz < SIZE; xyz++)
		{
			line1 |= BIT(xyz, xyz, xyz);
			line2 |= BIT(xyz, xyz, SIZE - 1 - xyz);
			line3 |= BIT(xyz, SIZE - 1 - xyz, xyz);
			line4 |= BIT(xyz, SIZE - 1 - xyz, SIZE - 1 - xyz);
		}
		lines.push_back(line1);
		lines.push_back(line2);
		lines.push_back(line3);
		lines.push_back(line4);
	}
	assert((int)lines.size() == LINES_NUM);
	for (int j = 0; j < LINES_NUM; j++) LINES[j] = lines[j];

	// 組 (l1, j) (l1 < j) の行番号 k = K0[l1] + (j - l1 - 1), K0[l1] = Σ_{a<l1} (75 - a)
	for (int l1 = 0; l1 < LINES_NUM; l1++)
	{
		const int k0 = l1 * (LINES_NUM - 1) - l1 * (l1 - 1) / 2;
		ROWBASE[l1] = (k0 - l1 - 1) * PNUM;
	}
}

// Board::count() と同じ。Me 視点で 自 n 個 = n, 敵 n 個 = -n, 両方あり = 4
static inline void line_counts(unsigned long long me, unsigned long long you, int c[LINES_NUM])
{
	// 分岐なしで書く(盤面ごとに結果がばらばらで分岐予測が当たらないため)。
	// 片方が 0 なら popcount(m) - popcount(y) が自 n 個 / 敵 -n 個 に一致する
	for (int i = 0; i < LINES_NUM; i++)
	{
		const unsigned long long m = me & LINES[i], y = you & LINES[i];
		const int v = __builtin_popcountll(m) - __builtin_popcountll(y);
		c[i] = (m && y) ? 4 : v;
	}
}

// ---- 教師データ ----
// 学習局面 1 つ。黒番(Me = 黒)の盤面と、同じ盤面が出た回数・教師値 p の和
struct Pos
{
	unsigned long long black, white;
	double sum_p;
	uint32_t cnt;
};

// 教師値 p(元コードと同じ式)
static double teacher_p(long long e)
{
	if (e < -1840) return 0.99;
	if (e > 1840) return 0.01;
	return 1.0 - 1.0 / (1.0 + exp(-(double)e / 400));
}

// 同じ盤面をまとめる(並べ替えて隣どうしを足す)
static void merge_same(vector<Pos>& v)
{
	sort(v.begin(), v.end(), [](const Pos& a, const Pos& b) {
		return a.black != b.black ? a.black < b.black : a.white < b.white;
	});
	size_t o = 0;
	for (size_t i = 0; i < v.size(); i++)
	{
		if (o > 0 && v[o - 1].black == v[i].black && v[o - 1].white == v[i].white)
		{
			v[o - 1].sum_p += v[i].sum_p;
			v[o - 1].cnt += v[i].cnt;
		}
		else v[o++] = v[i];
	}
	v.resize(o);
}

struct Dataset
{
	vector<Pos> pos;
	size_t games = 0;
	size_t samples = 0;  // まとめる前の学習局面数
};

// 1 行を整数列に分解する(区切りはカンマ、末尾カンマ可)
static int parse_ints(const char* s, long long* out, int cap)
{
	int n = 0;
	while (*s && n < cap)
	{
		while (*s == ',' || *s == ' ' || *s == '\t') s++;
		if (!*s || *s == '\n' || *s == '\r') break;
		char* end;
		const long long v = strtoll(s, &end, 10);
		if (end == s) break;
		out[n++] = v;
		s = end;
	}
	return n;
}

// record と second_evaluate を 1 行ずつ読み、学習局面を ds.pos に足す。
// raw が非 null なら、まとめる前の局面もそこへ入れる(--verify 用)
static bool load_pair(const char* record_path, const char* second_path, Dataset& ds, size_t max_games, vector<Pos>* raw)
{
	FILE* fr = fopen(record_path, "r");
	FILE* fs = fopen(second_path, "r");
	if (!fr || !fs)
	{
		fprintf(stderr, "ファイルを開けません: %s / %s\n", record_path, second_path);
		if (fr) fclose(fr);
		if (fs) fclose(fs);
		return false;
	}
	static char lr[1 << 14], ls[1 << 14];
	long long rec[80], sec[80];
	size_t loaded = 0, bad = 0;
	size_t merged_size = ds.pos.size();
	while (ds.games < max_games && fgets(lr, sizeof lr, fr) && fgets(ls, sizeof ls, fs))
	{
		const int nr = parse_ints(lr, rec, 80);
		const int ns = parse_ints(ls, sec, 80);
		if (nr == 0) continue;

		Pos buf[32];
		int nb = 0;
		unsigned long long side[2] = {0uLL, 0uLL};
		bool ok = true;
		for (int i = 0; i < 64 && i < nr && rec[i] < INF; i++)
		{
			if (rec[i] < 0 || rec[i] >= 16) { ok = false; break; }
			// 元コード: x = record % 4, y = 3 - record / 4 で place(x, y)
			const int x = (int)(rec[i] % 4), y = 3 - (int)(rec[i] / 4);
			const unsigned long long occ = side[0] | side[1];
			const unsigned long long col = 0x0001000100010001uLL << (x + y * SIZE);
			const unsigned long long bit = ((occ << SIZE * SIZE) | ((1uLL << SIZE * SIZE) - 1)) & ~occ & col;
			if (!bit) { ok = false; break; }
			side[i & 1] |= bit;

			// 勝ち手で打ち切る(不具合修正 (d))
			bool ended = false;
			for (int l = 0; l < LINES_NUM; l++)
				if ((side[i & 1] & LINES[l]) == LINES[l]) ended = true;
			if (ended) break;

			// i 奇数: 白が打った直後で黒番。教師値は evaluatessec[(i-1)/2] = CSV の (i-1)/2 列目
			if (!(i & 1)) continue;
			const int s = i >> 1;
			if (s >= ns || sec[s] <= -INF || sec[s] >= INF) continue;
			buf[nb++] = Pos{side[0], side[1], teacher_p(sec[s]), 1};
		}
		if (!ok) { bad++; continue; }

		ds.pos.insert(ds.pos.end(), buf, buf + nb);
		if (raw) raw->insert(raw->end(), buf, buf + nb);
		ds.samples += nb;
		ds.games++;
		loaded++;
		// 未統合の局面が増えすぎないよう、統合済みの 2 倍を超えたらまとめる(メモリのピークを抑える)
		if (ds.pos.size() > max<size_t>(2 * merged_size, 1 << 22))
		{
			merge_same(ds.pos);
			merged_size = ds.pos.size();
		}
	}
	fclose(fr);
	fclose(fs);
	printf("読込: %s  %zu 試合", record_path, loaded);
	if (bad) printf("(不正な棋譜 %zu 試合をスキップ)", bad);
	printf("\n");
	return true;
}

static inline double predict_q(long long training)
{
	if (training < -1840) return 0.01;
	if (training > 1840) return 0.99;
	return 1.0 / (1.0 + exp(-(double)training / 400));
}

// ---- 学習本体(ブロック版) ----
// 局面ごとに 2850 組の重みを引く(局面優先)と、重み表 730 KB と勾配表 1.4 MB へのランダムアクセスが
// 局面あたり 5700 回になり、キャッシュミスで律速する。
// そこで BLOCK 局面ずつまとめて、L1/L2 に収まる単位で計算する。
//   順伝播: 局面 8 個ずつ評価値をレジスタに持ち、相手ライン l2 を回して重みを AVX2 gather で足す。
//           ライン状態は転置して C[ライン][局面] に並べ、8 局面ぶんを 1 回で読む。
//           1 本目のライン l1 を固定すると重みの行 75 本(19 KB)だけを使うので L1 に載る。
//   逆伝播: 局面ごとに、l1 を固定した組 (l1, l2) ぶんの局所和 acc[l2][64] へ d を足す
//           (相手ライン 32 本ずつ、16 KB で L1 に載る)。
//           連続する加算は別アドレスになるので、同じ状態が続いても store→load の依存で止まらない。
//           局所和は勾配へ 1 回だけ足す。
// 実測(i7-1260P, ver7_1 全 65536 試合 = 78 万局面, 1 反復):
//   1 スレッド 2.7 s / 16 スレッド 0.85 s。
//   元コードは 500 試合 84 ms(1 スレッド)なので 65536 試合ぶんに換算するとおよそ 11 s。
//   このノート PC では 4 スレッドあたりから電力上限で頭打ちになる(デスクトップならもっと伸びるはず)。
static const int BLOCK = 2048;
static const int ACC_PAIRS = 32;  // 逆伝播の局所和を相手ライン何本ずつに区切るか(block_backward 参照)
static const uint8_t C_EMPTY = 3;  // cnt = 0。詰め物の局面はすべて空 → 状態 27(重み 0)

struct Block
{
	alignas(64) uint8_t C[LINES_NUM][BLOCK];  // C[l][s] = cnt + 3 (0..7)。順伝播用
	alignas(64) uint16_t R[BLOCK][80];        // R[s][l] = l * 64 + (cnt + 3)。逆伝播で組 (l1, l) の局所和の位置をそのまま引く
	alignas(64) int32_t tr[BLOCK];            // 評価値(元コードの training)
	alignas(64) double d[BLOCK];
	alignas(64) double acc[ACC_PAIRS * PNUM];
	int n, npad;                              // 局面数と、8 の倍数に切り上げた数
};

// 局面 [s0, s1) をブロックに詰める
static void fill_block(const Pos* pos, size_t s0, size_t s1, Block& B)
{
	int n = 0, c[LINES_NUM];
	for (size_t i = s0; i < s1; i++, n++)
	{
		line_counts(pos[i].black, pos[i].white, c);  // Me = 黒(推論側 board.count() と同じ視点)
		for (int l = 0; l < LINES_NUM; l++) B.C[l][n] = (uint8_t)(c[l] + 3), B.R[n][l] = (uint16_t)(l * PNUM + c[l] + 3);
	}
	B.n = n;
	B.npad = (n + 7) & ~7;
	for (int s = n; s < B.npad; s++)
		for (int l = 0; l < LINES_NUM; l++) B.C[l][s] = C_EMPTY, B.R[s][l] = (uint16_t)(l * PNUM + C_EMPTY);
}

static void block_forward(Block& B, const int32_t* __restrict w)
{
	const int npad = B.npad;
	int32_t* __restrict tr = B.tr;
	memset(tr, 0, sizeof(int32_t) * npad);
	int k0 = 0;  // 組 (l1, l1+1) の行番号
	for (int l1 = 0; l1 < LINES_NUM - 1; l1++)
	{
		const uint8_t* __restrict a = B.C[l1];
		const int32_t* __restrict wl = w + (k0 - l1 - 1) * PNUM;  // wl + l2 * 64 が組 (l1, l2) の行
		for (int s = 0; s < npad; s += 8)
		{
#ifdef __AVX2__
			const __m128i a8 = _mm_slli_epi16(_mm_loadl_epi64((const __m128i*)(a + s)), 3);  // 値 ≤ 7 なのでバイトをまたがない
			__m256i sum = _mm256_setzero_si256();
			for (int l2 = l1 + 1; l2 < LINES_NUM; l2++)
			{
				const __m128i b = _mm_loadl_epi64((const __m128i*)(B.C[l2] + s));
				const __m256i id = _mm256_cvtepu8_epi32(_mm_add_epi8(a8, b));
				sum = _mm256_add_epi32(sum, _mm256_i32gather_epi32(wl + l2 * PNUM, id, 4));
			}
			_mm256_store_si256((__m256i*)(tr + s), _mm256_add_epi32(_mm256_load_si256((const __m256i*)(tr + s)), sum));
#else
			for (int u = 0; u < 8; u++)
			{
				const int a8 = a[s + u] * 8;
				int32_t sum = 0;
				for (int l2 = l1 + 1; l2 < LINES_NUM; l2++) sum += wl[l2 * PNUM + a8 + B.C[l2][s + u]];
				tr[s + u] += sum;
			}
#endif
		}
		k0 += LINES_NUM - 1 - l1;
	}
}

// d[s] = Σp - m q を各組の状態ごとに足し込む。
// 局所和は相手ライン ACC_PAIRS 本ずつ(16 KB)に区切る。E コアの L1 は 32 KB、P コアは 48 KB を
// ハイパースレッドの 2 本で分け合うので、75 本ぶん(38 KB)を一度に持つと L1 から溢れて遅くなる
static void block_backward(Block& B, double* __restrict g)
{
	const int n = B.n;
	int k0 = 0;
	for (int l1 = 0; l1 < LINES_NUM - 1; l1++)
	{
		for (int lb = l1 + 1; lb < LINES_NUM; lb += ACC_PAIRS)
		{
			const int le = min(LINES_NUM, lb + ACC_PAIRS);
			const int m = le - lb;
			double* __restrict acc = B.acc;
			memset(acc, 0, sizeof(double) * m * PNUM);
			double* __restrict al = acc - lb * PNUM;  // al + l2 * 64 が組 (l1, l2) の局所和
			for (int s = 0; s < n; s++)
			{
				const uint16_t* __restrict r = B.R[s];
				const double dv = B.d[s];
				double* __restrict ap = al + (r[l1] & 7) * 8;
				for (int l2 = lb; l2 < le; l2++) ap[r[l2]] += dv;
			}
			double* __restrict gr = g + (k0 + lb - l1 - 1) * PNUM;
			for (int t = 0; t < m * PNUM; t++) gr[t] += acc[t];
		}
		k0 += LINES_NUM - 1 - l1;
	}
}

// 全教師局面について loss と勾配 Σ(p - q) を求める
static double loss_and_grad(const vector<Pos>& pos, const int32_t* w, double* grad, vector<vector<double>>& tgrad)
{
	const int T = (int)tgrad.size();
	const long long nblocks = (long long)((pos.size() + BLOCK - 1) / BLOCK);
	double loss = 0;
	#pragma omp parallel num_threads(T) reduction(+:loss)
	{
		double* g = tgrad[omp_get_thread_num()].data();
		memset(g, 0, sizeof(double) * NPARAM);
		Block* B = new Block;

		#pragma omp for schedule(dynamic, 1)
		for (long long bi = 0; bi < nblocks; bi++)
		{
			const size_t s0 = (size_t)bi * BLOCK;
			fill_block(pos.data(), s0, min(pos.size(), s0 + BLOCK), *B);
			block_forward(*B, w);
			for (int s = 0; s < B->n; s++)
			{
				const Pos& P = pos[s0 + s];
				const double q = predict_q(B->tr[s]);
				// m 個の同一局面ぶん: Σ_i [-p_i log q - (1 - p_i) log(1 - q)]
				loss += -P.sum_p * log(q) - (P.cnt - P.sum_p) * log1p(-q);
				B->d[s] = P.sum_p - P.cnt * q;
			}
			block_backward(*B, g);
		}
		delete B;

		// スレッド別の勾配を合計(パラメータ方向に分割)
		#pragma omp for schedule(static)
		for (int k = 0; k < NPARAM; k++)
		{
			double s = 0;
			for (int th = 0; th < T; th++) s += tgrad[th][k];
			grad[k] = s;
		}
	}
	return loss;
}

// ---- 検算用(--verify) ----
// bonanza_2line をそのまま書いた参照実装
static long long bonanza_2line_ref(unsigned long long me, unsigned long long you, const int32_t* w)
{
	int c[LINES_NUM];
	line_counts(me, you, c);
	long long ret = 0;
	int t = 0;
	for (int i = 0; i < LINES_NUM; i++)
		for (int j = i + 1; j < LINES_NUM; j++)
		{
			ret += w[t * PNUM + (c[i] + 3) * 8 + (c[j] + 3)];
			t++;
		}
	return ret;
}

// 局面を 1 つずつ(統合せずに)、2850 組を素直に回して loss と勾配を求める
static double loss_and_grad_naive(const vector<Pos>& raw, const int32_t* w, double* grad)
{
	memset(grad, 0, sizeof(double) * NPARAM);
	double loss = 0;
	int c[LINES_NUM];
	for (const Pos& P : raw)
	{
		line_counts(P.black, P.white, c);
		long long training = 0;
		int k = 0;
		for (int i = 0; i < LINES_NUM; i++)
			for (int j = i + 1; j < LINES_NUM; j++, k++)
				training += w[k * PNUM + (c[i] + 3) * 8 + (c[j] + 3)];
		const double p = P.sum_p, q = predict_q(training);
		loss += -p * log(q) - (1 - p) * log1p(-q);
		k = 0;
		for (int i = 0; i < LINES_NUM; i++)
			for (int j = i + 1; j < LINES_NUM; j++, k++)
				grad[k * PNUM + (c[i] + 3) * 8 + (c[j] + 3)] += p - q;
	}
	return loss;
}

static int verify(const Dataset& ds, const vector<Pos>& raw, const int32_t* w)
{
	// 1. ブロック版の順伝播 = bonanza_2line
	size_t mismatch = 0;
	Block* B = new Block;
	for (size_t s0 = 0; s0 < ds.pos.size(); s0 += BLOCK)
	{
		fill_block(ds.pos.data(), s0, min(ds.pos.size(), s0 + BLOCK), *B);
		block_forward(*B, w);
		for (int s = 0; s < B->n; s++)
		{
			const Pos& P = ds.pos[s0 + s];
			const long long ref = bonanza_2line_ref(P.black, P.white, w);
			if (B->tr[s] != ref && mismatch++ < 5) printf("不一致: 局面 %zu fast=%d ref=%lld\n", s0 + s, B->tr[s], ref);
		}
	}
	delete B;
	printf("verify 評価値: %zu 局面中 不一致 %zu\n", ds.pos.size(), mismatch);

	// 2. 統合 + ブロック版の loss・勾配 = 統合なしで素直に計算した値(足す順序の違いによる誤差は許す)
	vector<double> g1(NPARAM), g2(NPARAM);
	vector<vector<double>> tgrad(omp_get_max_threads(), vector<double>(NPARAM));
	const double L1 = loss_and_grad(ds.pos, w, g1.data(), tgrad);
	const double L2 = loss_and_grad_naive(raw, w, g2.data());
	double gmax = 0;
	for (int k = 0; k < NPARAM; k++)
		if (!is_fixed_zero(k % PNUM)) gmax = max(gmax, fabs(g1[k] - g2[k]));
	printf("verify 学習: loss 高速版=%.9f 素直版=%.9f, 勾配の最大差 %.3g\n", L1, L2, gmax);
	if (fabs(L1 - L2) > 1e-9 * fabs(L2) || gmax > 1e-6) mismatch++;
	return mismatch ? 1 : 0;
}

int main(int argc, char** argv)
{
	enable_utf8_console();
	setvbuf(stdout, nullptr, _IOFBF, 1 << 16);

	vector<pair<string, string>> data;
	size_t max_games = (size_t)-1;
	string out_path = "/yonmoku/feature/feature.csv";
	int threads = omp_get_max_threads();
	int restarts = 50, iters = 1000;
	unsigned long long seed = random_device{}();
	long long verify_games = -1;

	for (int a = 1; a < argc; a++)
	{
		string s = argv[a];
		auto need = [&](int n) { if (a + n >= argc) { fprintf(stderr, "%s に引数が足りません\n", s.c_str()); exit(2); } };
		if (s == "-d") { need(2); data.emplace_back(argv[a + 1], argv[a + 2]); a += 2; }
		else if (s == "-g") { need(1); max_games = strtoull(argv[++a], nullptr, 10); }
		else if (s == "-o") { need(1); out_path = argv[++a]; }
		else if (s == "-j") { need(1); threads = max(1, atoi(argv[++a])); }
		else if (s == "-t") { need(1); restarts = atoi(argv[++a]); }
		else if (s == "-n") { need(1); iters = atoi(argv[++a]); }
		else if (s == "-s") { need(1); seed = strtoull(argv[++a], nullptr, 10); }
		else if (s == "--verify") { need(1); verify_games = atoll(argv[++a]); }
		else { fprintf(stderr, "不明なオプション: %s\n", s.c_str()); return 2; }
	}
	if (data.empty())
		data.emplace_back("/yonmoku/teacher/record_ver7_1.csv", "/yonmoku/teacher/second_evaluate_ver7_1.csv");

	init_lines();

	if (verify_games >= 0) max_games = (size_t)verify_games;
	Dataset ds;
	vector<Pos> raw;
	for (auto& [r, s] : data)
		if (!load_pair(r.c_str(), s.c_str(), ds, max_games, verify_games >= 0 ? &raw : nullptr)) return 1;
	merge_same(ds.pos);
	ds.pos.shrink_to_fit();
	printf("試合数 = %zu, 学習局面数 = %zu → 同一盤面をまとめて %zu, 教師データ %.1f MB\n",
		ds.games, ds.samples, ds.pos.size(), ds.pos.size() * sizeof(Pos) / 1048576.0);
	if (ds.pos.empty()) { fprintf(stderr, "学習局面がありません\n"); return 1; }

	mt19937 rng((unsigned)seed);
	uniform_int_distribution<int> dist(-500, 500);
	vector<int32_t> param(NPARAM), best_param(NPARAM);
	for (int k = 0; k < PAIRS; k++)
		for (int p = 0; p < PNUM; p++)
			param[k * PNUM + p] = is_fixed_zero(p) ? 0 : dist(rng);

	if (verify_games >= 0) return verify(ds, raw, param.data());

	printf("number of thread = %d, seed = %llu\n", threads, seed);
	fflush(stdout);

	vector<vector<double>> tgrad(threads, vector<double>(NPARAM));
	vector<double> differ(NPARAM);
	vector<int32_t> conticnt(NPARAM, 0);
	vector<int8_t> contiflag(NPARAM);

	double bestloss = INF;
	best_param = param;
	const auto t_start = chrono::steady_clock::now();

	for (int t = 0; t < restarts; t++)
	{
		bool flag = false;
		fill(contiflag.begin(), contiflag.end(), 2);  // contiflag 初期化
		const double firstloss = bestloss;
		printf("firstloss = %.6f\n", firstloss);

		for (int n = 0; n < iters; n++)
		{
			const auto st = chrono::steady_clock::now();
			const double loss = loss_and_grad(ds.pos, param.data(), differ.data(), tgrad);

			if (loss < bestloss)
			{
				best_param = param;
				bestloss = loss;
			}

			const double th = pow(1.05, n);  // 元: 000 + pow((double)1.05, n)
			long long cnt = 0;
			for (int k = 0; k < NPARAM; k++)
			{
				if (is_fixed_zero(k % PNUM))
				{
					// 元コードでは勾配が常に 0 なので else 節(正則化)に入る。値は 0 のまま
					cnt++;
					continue;
				}
				int step;
				if (differ[k] > th)
				{
					step = 1;
					if (contiflag[k] == 1) conticnt[k]++;
					else conticnt[k] = 0;
					contiflag[k] = 1;
				}
				else if (differ[k] < -th)
				{
					step = -1;
					if (contiflag[k] == -1) conticnt[k]--;
					else conticnt[k] = 0;
					contiflag[k] = -1;
				}
				else
				{
					step = 0;
					conticnt[k] = 0;
					contiflag[k] = 0;
					cnt++;
					// 正則化
					if (param[k] > 0) param[k]--;
					else if (param[k] < 0) param[k]++;
				}
				param[k] += step + conticnt[k];
			}

			const double sec = chrono::duration<double>(chrono::steady_clock::now() - st).count();
			printf("n = %d, loss = %.6f  (%.3f s)\n", n, loss, sec);
			fflush(stdout);

			if (cnt == (long long)NPARAM)  // 収束判定
			{
				printf("converge\n");
				if (firstloss - bestloss > 0.1)  // 次に行く
				{
					printf("\033[31mrefined\033[m\nt = %d\nloss = %.6f\n", t, bestloss);
					param = best_param;
					break;
				}
				else  // 次に行かない
				{
					printf("NOT refined, loss = %.6f\n", bestloss);
					flag = true;
					break;
				}
			}
		}
		if (flag) break;
	}

	FILE* fo = fopen(out_path.c_str(), "w");
	if (!fo) { fprintf(stderr, "出力先を開けません: %s\n", out_path.c_str()); return 1; }
	for (int k = 0; k < PAIRS; k++)
	{
		for (int p = 0; p < PNUM; p++) fprintf(fo, "%d,", best_param[k * PNUM + p]);
		fprintf(fo, "\n");
	}
	fclose(fo);

	const double total = chrono::duration<double>(chrono::steady_clock::now() - t_start).count();
	printf("\nloss = %.6f, 出力: %s, 学習時間 %.1f s\n", bestloss, out_path.c_str(), total);
	return 0;
}
