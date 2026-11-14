#include <stdlib.h>
#include <omp.h>

#include "../code/common.hpp"
#include "../code/board.hpp"
#include "../code/core_feature.hpp"   // core_feat::counts(探索側 code/evaluate_core.hpp と同じ関数)
#include "evaluate_gd_both.hpp"
#include "gd_weights_out.hpp"
#include "console_utf8.hpp"

// main_gd_both.cpp に「核 2 マスの全状態」(6 本 / バケット)のパラメータを足した学習コード。
// 探索側は code/main_core.cpp(評価関数は code/evaluate_core.hpp)。
// 設計: docs/設計書/評価関数パラメータ/investigation-new-eval-features.md §2.6 D
//
// 流用元 main_gd_both.cpp との差分は次の 5 点だけで、勾配降下法の本体・教師値の変換・
// 制約C フィルタ・バケット定義は 1 行も変えていない。
//   1. pnum = 29 → 35。追加の 6 本(添字 29..34)は core_feat::counts() の out[0..5]
//        29: z=1 自 / z=2 空    30: z=1 敵 / z=2 空
//        31: 自 自              32: 自(下) 敵(上)
//        33: 敵(下) 自(上)      34: 敵 敵
//      既存 29 本は流用元どおり ps[p]=1 の単位ベクトルで evaluate_feature() を叩いて作る。
//      追加 6 本は評価値がパラメータについて線形なので、出現数を core_feat::counts() で直接入れる。
//      turn >= 60 では 0(探索側 EvalFnCore が turn >= 60 で核の項を足さないのに合わせる)。
//   2. A 配列を int → short にし、定数項だけ別の int 配列 A0 に分けた(メモリ対策。§5.2)。
//        流用元の int A[100001][64][30]  = 732 MiB
//        そのまま 35 本にすると          = 879 MiB
//        本ファイル short A[..][35] + int A0 = 427 MiB + 24 MiB
//      特徴量は出現数(高々 76)で short に収まる。定数項は turn = 60 の局面で
//      INF - 100000 になり short に収まらないので int のまま残す。
//      収まらない値が出たら構築時に検出して中止する。学習ループで読む値は流用元と同一。
//   3. 構築後に、追加 6 本の平均出現数を側 × バケットごとに表示する(検証用。調査書 §2.6 の表と比較できる)
//   4. 重みファイルは version: 2 で出力し、各セクションに core = 6 個 の行を足す
//      (読み込みは code/eval_weights_core.hpp。既存 7 キーの並びと書式は流用元と同一)
//   5. 出力名(WEIGHTS_NAME / OUTPUT_WEIGHTS_PATH)を既存モデルと別の名前にした
//
// ---- 以下は流用元 main_gd_both.cpp の説明 ----
//
// 先手(fir)と後手(sec)の勾配降下法を 1 本にまとめ、8 回分(2 側 × 4 バケット)の結果を
// weights/verX_Y.txt と同じ書式でまとめて出力する。
//
// 元になったファイル:
//   MachineLearning/main_gd_alpha_all.cpp                     (先手 4 バケット)
//   MachineLearning/yonmoku_gradient_descent_second_alpha_all.cpp (後手 4 バケット)
// 勾配降下法の本体は main_gd_alpha_all.cpp:189-419 をそのまま複写し、
// 側によって変わる次の 3 点だけを引数にした。
//   1. 参照する turn の範囲   fir: 4~17/18~31/32~45/46~59 (record 添字 奇数)
//                             sec: 5~18/19~32/33~46/47~60 (record 添字 偶数)
//   2. 教師値の配列           fir: evaluatessec / sec: evaluatesfir
//                             添字はどちらも i / 2(奇数 i では (i-1)/2 == i/2)
//   3. 外側の再試行回数       SIDES[] の restart(元コードは先手 30 / 後手 40)
//
// 特徴量行列 A の構築は 1 回で済む。evaluate_feature() は手番で分岐し、
// record 添字が奇数なら黒手番 = 先手用、偶数なら白手番 = 後手用の値を返すため、
// 同じ A を先手学習は奇数要素、後手学習は偶数要素として読むだけでよい。
// (詳細は evaluate_gd_both.hpp の冒頭コメント)
//
// ===== 制約C フィルタ(USE_LEAF_FILTER)=====
// 探索は「いま置けるマスの上に双方どちらのリーチも無い」局面でしか評価関数を呼ばない
// (ai_player_pvs_inc_id.hpp:148-158)。相手に即勝ち手がある局面は level<=0 でも
// 評価を返さず受け手に絞って更に深く読むため、その評価値は一度も使われない。
// ところが教師局面のうちその条件を満たすのは 83.7% で、残り 16.3% は
// 「評価関数が何を返そうと探索結果に影響しない局面」である。
// そこを学習から外すと、実際に使われる局面での当てはめが良くなる。
//   実測(テスト loss, 特徴量は 29 本のまま):
//     fir b0 -0.00039 / fir b1 -0.00108 / sec b0 -0.00084 / sec b1 -0.00274
// 調査: docs/設計書/評価関数パラメータ/investigation-training-filter.md
// USE_LEAF_FILTER=0 でビルドすれば導入前と完全に同じ挙動に戻る。

int evaluatesfir[100000][34] = {};
int evaluatessec[100000][34] = {};
int record[100001][65] = {};

const int pnum_base = 29;                   // 既存パラメータ(evaluate_gd_both.hpp の ps[0..28])
const int pnum = pnum_base + core_feat::NUM; // + 核 2 マスの全状態 6 本 = 35
short A[100001][64][pnum];                  // 特徴量(出現数)。流用元の A[t][i][0..pnum-1] に当たる
int   A0[100001][64];                       // 定数項。流用元の A[t][i][pnum] に当たる

// 探索が葉評価を呼ぶ局面か(= 制約C)。ai_player_pvs_inc_id.hpp:148-158 と同一条件。
//   (hand & Board::reach(Me)) == 0 && (hand & Board::reach(You)) == 0
// 設計: docs/設計書/評価関数パラメータ/investigation-training-filter.md
bool leafC[100001][64] = {};

// 制約C を満たさない局面(= 探索が評価関数を呼ばない局面)を学習から外すか。
//   1 = 外す(既定)。A 行列もその分だけ作らないので構築も速くなる。
//   0 = 外さない。導入前と完全に同じ挙動に戻る。
#ifndef USE_LEAF_FILTER
#define USE_LEAF_FILTER 1
#endif

// ===== 設定 =====================================================
// 教師データと局数。main_gd_alpha_all.cpp の現在の設定に合わせてある。
// (後手版 yonmoku_gradient_descent_second_alpha_all.cpp は ver7_2_new / 81920 の
//  ままだったが、1 モデルは同一の教師データから作る必要があるので統一した)
static const char *INPUT_FIRST_EVALUATE = "/yonmoku/teacher/first_evaluate_ver8_2.csv";
static const char *INPUT_SECOND_EVALUATE = "/yonmoku/teacher/second_evaluate_ver8_2.csv";
static const char *INPUT_RECORD          = "/yonmoku/teacher/record_ver8_2.csv";
static const int   gameNum               = 93600;

// 出力する weights ファイルの name 行。weights/verX_Y.txt の name: に入る。
static const char *WEIGHTS_NAME = "ver1.0";

// 出力先。空文字なら標準出力のみ。ファイル名を書くとそのファイルにも書き出す。
// 出力は version: 2(core 付き)なので、読めるのは code/main_core.cpp 系(eval_weights_core.hpp)だけ。
// 既存の match_weights / main_alpha_pvs_eval_inc_tbl_id_w は version: 2 を拒否する。
// core 付きモデルは weights/core/ 配下に置く(既存評価関数のモデルは weights/alpha/。main_gd_both.cpp)。
static const char *OUTPUT_WEIGHTS_PATH = "/yonmoku/GitHub/weights/core/ver1_0_core.txt";
// ================================================================

// 学習する側とバケットの定義。
// turn_bucket は weights/README.md のとおり 先手 (turn-4)/14、後手 (turn-5)/14。
// record 添字 i に石を置いた直後の turn は i+2 なので、
//   先手 bucket0 = turn 4~17  -> i = 3,5,..,15   (i < 17)
//   後手 bucket0 = turn 5~18  -> i = 4,6,..,16   (i < 18)
// のように 1 つずつずれる。
struct BucketSpec
{
	int begin;  // for(int i = begin; i < end; i = i + 2) の begin
	int end;    // 同上 end
	const char *label;
};

struct SideSpec
{
	const char *name;        // "fir" / "sec"
	int restart;             // 外側の再試行回数
	const char *teacher_name;
	BucketSpec bucket[4];
};

static const SideSpec SIDES[2] =
{
	{"fir", 40, "evaluatessec", {{ 3, 17, "4~17"}, {17, 31, "18~31"}, {31, 45, "32~45"}, {45, 59, "46~59"}}},
	{"sec", 40, "evaluatesfir", {{ 4, 18, "5~18"}, {18, 32, "19~32"}, {32, 46, "33~46"}, {46, 60, "47~60"}}},
};

// 1 側 × 1 バケット分の勾配降下法。
// 中身は main_gd_alpha_all.cpp:189-419 の複写(置換したのは teacher と restart のみ)。
static void run_gd(const int rangeBegin, const int rangeEnd, const int restart,
                   const int (*teacher)[34], const int threadNum,
                   int bestOut[pnum], long double *bestLossOut)
{
	long double bestloss[threadNum][pnum + 1];

	// このバケットの学習局面で一度も現れない(A が全局面で 0 の)パラメータを調べる。
	// 条件は下の学習ループと同一。そのようなパラメータは勾配が常に 0 で初期値から動かないため、
	// 初期値を 0 にして、出力に乱数の初期値が残らないようにする。
	// 判定は和ではなく「0 でない値が 1 件でもあるか」(既存 29 本は差分なので負の値もあり得る)。
	bool appeared[pnum] = {};
	for(int t = 1; t <= gameNum; t++)
	{
		for(int i = rangeBegin; i < rangeEnd; i = i + 2)
		{
#if USE_LEAF_FILTER
			if(!(record[t][i] < INF && leafC[t][i])) continue;
#else
			if(!(record[t][i] < INF)) continue;
#endif
			if(!((teacher[t][i / 2] > -INF) && (teacher[t][i / 2] < INF))) continue;
			for(int p = 0; p < pnum; p++) if(A[t][i][p] != 0) appeared[p] = true;
		}
	}
	cout << "unused parameters (初期値を 0 に固定) = ";
	for(int p = 0; p < pnum; p++) if(!appeared[p]) cout << p << ",";
	cout << endl;

    //ここから最急降下法
	# pragma omp parallel
    {
		int thread = omp_get_thread_num();
        long double loss;
        long double firstloss;
        bestloss[thread][pnum] = INF;

        uniform_int_distribution<int> dist(-1500, 1500);
		int random_parameter[pnum] = {};

		for(int i = 0; i < pnum; i++)random_parameter[i] = dist(rng);
		//一度も現れないパラメータは 0 にする(乱数は全本数ぶん引いてから上書きするので、他の初期値は変わらない)
		for(int i = 0; i < pnum; i++)if(!appeared[i])random_parameter[i] = 0;
		for(int i = 0; i < pnum; i++)cout << random_parameter[i] << ",";
		cout << endl;

		for(int t = 0; t < restart; t++)
		{
			bool flag = false;
			int conticnt[pnum] = {};//連続何回目かを入れる
			int contiflag[pnum] = {};//前回どの方向に進んだかを入れる
			for(int i = 0; i < pnum; i++)contiflag[i] = 2;//contiflag初期化
			firstloss = bestloss[thread][pnum];//firstloss初期化
			cout << "firstloss = " << firstloss ;
			cout << endl;

			for(int n = 0; n < 1000; n++)
			{
				double differ[pnum] = {};
				for(int i = 0; i < pnum; i++)differ[i] = 0;

				loss = 0;
				for(int t = 1; t <= gameNum; t++)
				{
					//for(int i = 0; i < 64; i++)
					// 学習する turn の範囲。呼び出し側の BucketSpec で切り替える。
					for(int i = rangeBegin; i < rangeEnd; i = i + 2)
					{
#if USE_LEAF_FILTER
						if(record[t][i] < INF && leafC[t][i])
#else
						if(record[t][i] < INF)
#endif
						{
							//if((i % 2 == 1) && (teacher[t][i / 2] > -INF) && (teacher[t][i / 2] < INF))
							if((teacher[t][i / 2] > -INF) && (teacher[t][i / 2] < INF))
							{
								//int training_old = evaluate_pointfir_layer_intersection(c);
								int training = A0[t][i];
								//for(int p = 0; p < pnum; p++) training += parameter[p] * A[t][i][p];
								for(int p = 0; p < pnum; p++) training += random_parameter[p] * A[t][i][p];
								//assert(training == training_old);
								long double p;
								long double q;

								if(teacher[t][i / 2] < -1840) p = 0.99;
								else if(teacher[t][i / 2] > 1840) p = 0.01;
								else p = 1 - 1/(1 + exp((long double)-(teacher[t][i / 2])/400));
								if(training < -1840) q = 0.01;
								else if(training > 1840) q = 0.99;
								else q = 1/(1 + exp((long double)-(training)/400));
								/*long double p = 1 - 1/(1 + exp((long double)-(teacher[t][i / 2] + 112)/200));
								long double q = 1/(1 + exp((long double)-(training)/200));
								if(q < 0.01) q = 0.01;
								else if(q > 0.99) q = 0.99;
								if(p < 0.01) p = 0.01;
								else if(p > 0.99) p = 0.99;*/
								//cout << "p=" << p << "," << "q=" << q << "," << training << endl;
								loss += -p*log(q) - (1 - p)*log1p(-q);
								//cout << "loss[" << i << "]=" << loss << endl;
								for(int j = 0; j < pnum; j++)
								{
									differ[j] += A[t][i][j]*(p-q);
								}
							}
						}
					}
				}
				//この時点でn回目の時のlossが求まる



				if(loss < bestloss[thread][pnum])
				{
					// cout << "(thread,t,n)=" << "(" << thread << "," << t << "," << n << ") ";
					//cout << "m = " << m << ", t = " << t << ", n = " << n << ",";
					for(int i = 0; i < pnum; i++)
					{
						bestloss[thread][i] = random_parameter[i];
						//cout << parameter[i] << ",";
						// cout << random_parameter[i] << ",";
					}
					//cout << "betterloss = " << betterloss << ",";
					// cout << "loss = " << loss << endl;
					// betterloss = loss;
					bestloss[thread][pnum] = loss;
				}

				{//途中経過を表示する
					// cout << "n = " << n << ",";
					// for(int i = 0; i < pnum; i++)
					// {
					// 	cout << random_parameter[i] << ",";
					// }
					// //cout << "betterloss = " << betterloss << ",";
					// cout << "loss = " << loss << endl;
				}

				int cnt = 0;

				for(int i = 0; i < pnum; i++)
				{
					{
						if(differ[i] > 000 + pow((double)1.05, n))//基本は9000+pow(1.15,n)1.05
						{
							differ[i] = 1;
							if(contiflag[i] == 1)conticnt[i]++;
							else conticnt[i] = 0;
							contiflag[i] = 1;
						}
						else if(differ[i] < -000 - pow((double)1.05, n))
						{
							differ[i] = -1;
							if(contiflag[i] == -1)conticnt[i]--;
							else conticnt[i] = 0;
							contiflag[i] = -1;
						}
						else
						{
							differ[i] = 0;
							conticnt[i] = 0;
							contiflag[i] = 0;
							cnt++;
						}
						//parameter[i] = parameter[i] + differ[i];
						//assert(contiflag[i] == -1 || contiflag[i] == 0 || contiflag[i] == 1);
						random_parameter[i] = random_parameter[i] + differ[i] + conticnt[i];
					}
				}
				if(cnt == pnum) //収束判定
				{
					cout << "converge" << endl;
					if(firstloss - bestloss[thread][pnum] > 0.1)//次に行く
					{
						cout << "\033[31mrefined\033[m" << endl;
                        cout << "thread = " << thread << ", t = " << t << endl;
						for(int i = 0; i < pnum; i++)
						{
							// bestloss[thread][i] = random_parameter[i];
							//cout << parameter[i] << ",";
							// cout << random_parameter[i] << ",";
							random_parameter[i] = bestloss[thread][i];
						}
						// bestloss[thread][pnum] = betterloss;
						cout << "loss = " << bestloss[thread][pnum] << endl;
						break;
					}
					else//次に行かない
					{
						// cout << "NOT refined, loss = " << firstloss << endl;
						cout << "NOT refined, loss = " << bestloss[thread][pnum] << endl;
                        cout << "thread = " << thread << endl;
						// bestloss[thread][pnum] = betterloss;
						flag = true;
						break;
					}
					//"\033[31m(Black)\033[m";
					//return 0;
				}

				/*
				if(bestn == 0)
				betterloss = 2*loss;
				//betterloss = 134819;
				bestn = INF;
				if(loss <= betterloss)
				{
					cout << "n = " << n << ",";
					for(int i = 0; i < pnum; i++)
					{
						cout << ps[i] << ",";
					}
					//cout << "betterloss = " << betterloss << ",";
					cout << "loss = " << loss << endl;
					betterloss = loss;
					h = 0;
				}
				else
				{
					h++;
					if(h % 2000 == 0)cout << "n = " << n << "/" << pow(3, pnum) << endl;
				}
				//cout << "betterloss = " << betterloss << endl;
				*/
			}
			if(flag == true)break;
		}
    }

	int bestOne[pnum + 1];
	long double bestOneLoss;   // bestloss[][] と同じ型にする(float だと有効 7 桁で loss の下位桁が落ち、最良スレッドの選択もぶれる)
	for(int i = 0; i < pnum; i++){
		bestOne[i] = bestloss[0][i];
	}
	bestOne[pnum] = 0;
	bestOneLoss = bestloss[0][pnum];

	for(int m = 0; m < threadNum; m++)
	{
		cout << "thread = " << m << ",  ";
		for(int i = 0; i < pnum; i++)
		{
			cout << bestloss[m][i] << ",";
		}
		cout << "loss = " << bestloss[m][pnum];
		cout << endl;
		if(bestOneLoss > bestloss[m][pnum]){
			for(int i = 0; i < pnum; i++){
				bestOne[i] = bestloss[m][i];
			}
			bestOne[pnum] = m;
			bestOneLoss = bestloss[m][pnum];
		}
	}
	cout << endl;
	cout << "best thread = " << bestOne[pnum] << ",  ";
	cout << endl;
	for(int i = 0; i < pnum; i++){
		cout << bestOne[i] << ",";
	}
	cout << "loss = " << bestOneLoss;
	cout << endl;

	for(int i = 0; i < pnum; i++) bestOut[i] = bestOne[i];
	*bestLossOut = bestOneLoss;
}

// 重みファイル(version: 2 = core 付き)を出力する。
// gdout::dump_weights_file()(gd_weights_out.hpp)と同じ行整形で、違いは次の 2 点だけ。
//   ・version: 1 → version: 2
//   ・各セクションの末尾に core = w[29..34] の行を足す
// 読み込みは code/eval_weights_core.hpp の EvalWeightsCore::load()。
// fir[4][pnum] / sec[4][pnum] はバケット順。w[0..28] の並びは gd_weights_out.hpp の対応表どおり。
static void dump_core_weights_file(ostream &os, const string &name,
                                   const int fir[4][pnum], const int sec[4][pnum],
                                   const long double *fir_loss, const long double *sec_loss)
{
	os << "# 立体四目並べ 評価関数重み(核 2 マスの全状態 core 付き)\n";
	os << "version: 2\n";
	os << "name: " << (name.empty() ? string("unnamed") : name) << "\n";
	gdout::put_loss_comments(os, fir_loss, sec_loss);
	for (int s = 0; s < 2; s++)
	{
		const char *side = (s == 0) ? "fir" : "sec";
		for (int b = 0; b < 4; b++)
		{
			const int *w = (s == 0) ? fir[b] : sec[b];
			gdout::put_bucket(os, side, b, w);   // 見出し + 既存 7 キー(w[0..28] のみ参照)
			gdout::put_key(os, "core", vector<int>(w + pnum_base, w + pnum));
		}
	}
}

// 学習を始める前に OUTPUT_WEIGHTS_PATH を検査する。
//   ・同名のファイルが既にある      -> 上書きしてよいか聞く。y 以外なら中止する。
//   ・無い                          -> 同じ場所へ一時ファイルを作れるかだけ確かめる。
// 数時間走らせた後で「開けなかった」「消したくないファイルを潰した」と気付くのを防ぐ。
//
// 問い合わせは標準エラーへ出す。標準出力をログへリダイレクトして実行しても
// プロンプトが画面に残るようにするため。
// 判定は fopen で行う(ofstream で開くとその時点で中身が消えてしまう)。
static bool check_output_path(const char *path)
{
	if(path[0] == 0) return true;//標準出力のみ。検査するものがない

	FILE *fp = fopen(path, "r");
	if(fp)
	{
		fclose(fp);
		cerr << endl;
		cerr << "出力先に同名のファイルがあります: " << path << endl;
		cerr << "上書きすると元の重みは失われます(weights/README.md は上書き禁止としています)。" << endl;
		cerr << "上書きして実行しますか? [y/N]: " << flush;

		string ans;
		if(!getline(cin, ans))
		{
			cerr << endl << "入力を読めませんでした。安全側に倒して中止します。" << endl;
			return false;
		}
		//前後の空白を落として小文字化
		const size_t a = ans.find_first_not_of(" \t\r\n");
		const size_t b = ans.find_last_not_of(" \t\r\n");
		ans = (a == string::npos) ? "" : ans.substr(a, b - a + 1);
		for(size_t i = 0; i < ans.size(); i++) ans[i] = (char)tolower((unsigned char)ans[i]);

		if(!(ans == "y" || ans == "yes"))
		{
			cerr << "中止しました。OUTPUT_WEIGHTS_PATH(main_gd_core.cpp の設定部)を"
			     << "別の名前に変えてから実行し直してください。" << endl;
			return false;
		}
		cerr << "上書きして続行します。" << endl;
		return true;
	}

	//まだ無い場合は、そこへ書けるかどうかだけ確かめる(本番のファイルは最後に作る)
	const string probe = string(path) + ".writetest.tmp";
	FILE *wp = fopen(probe.c_str(), "w");
	if(!wp)
	{
		cerr << endl;
		cerr << "出力先に書き込めません: " << path << endl;
		cerr << "フォルダが存在するか、パスの綴りを確認してください。" << endl;
		return false;
	}
	fclose(wp);
	remove(probe.c_str());
	cout << "output weights file = " << path << " (新規作成)" << endl;
	return true;
}

int main()
{
	//コンソールの出力コードページを UTF-8 に合わせる(日本語の文字化け対策)
	//下の確認メッセージも日本語なので、必ずここより前に呼ぶこと
	enable_utf8_console();

	//重い処理に入る前に出力先を確かめる
	if(!check_output_path(OUTPUT_WEIGHTS_PATH)) return 1;

	init_lines();

	std::ifstream ifs_first_evaluate (INPUT_FIRST_EVALUATE);
	std::ifstream ifs_second_evaluate (INPUT_SECOND_EVALUATE);
	std::ifstream ifs_record (INPUT_RECORD);

	std::string str_buf;

	int t = 1;
	while(getline(ifs_first_evaluate, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatesfir[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_second_evaluate, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatessec[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_record, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			record[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}

	//Aに各盤面のパラメータの出現数を入れる
	//evaluate_feature() は手番で分岐するので、奇数 i には先手用、偶数 i には後手用の
	//特徴量が入る。先手学習は奇数 i、後手学習は偶数 i しか読まないため、これで足りる。
    for(int n = 1; n <= gameNum; n++)
    {
        Board c;
        for(int i = 0; i < 64; i++)
        {
            if(record[n][i] < INF)
            {
                int x = record[n][i] % 4;
                int y = 3 - (record[n][i] / 4);
                c.place(x, y);

                {//制約C の判定(ai_player_pvs_inc_id.hpp:148-158 と同一)
                    // place() が Me/You を入れ替えるので、この時点の c.Me は「次に指す側」。
                    // 探索側の board.b.Me(= rMe_raw の引数)と同じ向きなので読み替えは要らない。
                    // Board::reach() は相手の石で埋まったマスも立てるが、hand(空きマス)と
                    // AND を取るので落ちる。探索側の判定と完全に一致する。
                    const unsigned long long hand = c.valid_move();
                    leafC[n][i] = !(hand & Board::reach(c.Me)) && !(hand & Board::reach(c.You));
                }
#if USE_LEAF_FILTER
                // 学習ループが読まない局面なので A も作らない(構築が約 16% 速くなる)。
                // A は 0 初期化済みで、この i は学習ループ側でも弾かれるため値は参照されない。
                if(!leafC[n][i]) continue;
#endif

                //既存 29 本: 流用元と同じく単位ベクトルで評価関数を叩く(Af[pnum_base] が定数項)
                int Af[pnum_base + 1];
                for(int p = 0; p <= pnum_base; p++)
                {
                    int ps[pnum_base];
                    for(int i = 0; i < pnum_base; i++)
                    {
                        ps[i] = 0;
                    }
                    if (p < pnum_base) ps[p] = 1;
                    gd::set_parameters(ps);
                    Af[p] = gd::evaluate_feature(c);
                }
                //定数項の影響を除く
                for(int p = 0; p < pnum_base; p++) Af[p] -= Af[pnum_base];

                //追加 6 本: 核 2 マスの全状態の本数。c.Me は「次に指す側」= 探索側の board.b.Me と同じ向き
                int Fc[core_feat::NUM] = {};
                if(c.turn() < 60) core_feat::counts(c.Me, c.You, Fc);

                A0[n][i] = Af[pnum_base];
                for(int p = 0; p < pnum; p++)
                {
                    const int v = (p < pnum_base) ? Af[p] : Fc[p - pnum_base];
                    if(v < SHRT_MIN || v > SHRT_MAX)
                    {
                        cerr << "特徴量が short に収まらない: game " << n << ", record 添字 " << i
                             << ", パラメータ " << p << ", 値 " << v << endl;
                        return 1;
                    }
                    A[n][i][p] = (short)v;
                }
            }
        }
    }

    {//追加 6 本(核 2 マスの全状態)の平均出現数を側 x バケットごとに表示する(検証用)
        // 学習ループと同じ条件(制約C フィルタ・教師値が有効)の局面で平均を取る。
        // 調査書 §2.6 の「平均本数(fir b1)」列と同じ量(同じ教師データなら一致するはず)。
        cout << endl;
        cout << "core features (平均本数 / 局面。学習に使う局面のみ)" << endl;
        {
            string head(15, ' ');   // "  [fir.bucket0]" の幅
            char buf[32];
            for(int k = 0; k < core_feat::NUM; k++) { snprintf(buf, sizeof(buf), "  %7s", core_feat::NAME[k]); head += buf; }
            cout << head << "      局面数" << endl;
        }
        for(int s = 0; s < 2; s++)
        {
            const SideSpec &side = SIDES[s];
            const int (*teacher)[34] = (s == 0) ? evaluatessec : evaluatesfir;
            for(int b = 0; b < 4; b++)
            {
                long long used = 0;
                long long sum[core_feat::NUM] = {};
                for(int n = 1; n <= gameNum; n++)
                    for(int i = side.bucket[b].begin; i < side.bucket[b].end; i = i + 2)
                    {
#if USE_LEAF_FILTER
                        if(!(record[n][i] < INF && leafC[n][i])) continue;
#else
                        if(!(record[n][i] < INF)) continue;
#endif
                        if(!((teacher[n][i / 2] > -INF) && (teacher[n][i / 2] < INF))) continue;
                        used++;
                        for(int k = 0; k < core_feat::NUM; k++) sum[k] += A[n][i][pnum_base + k];
                    }
                //cout の書式状態(精度など)を変えると後段の loss 表示が変わるので snprintf で整形する
                char buf[32];
                string row = string("  [") + side.name + ".bucket" + to_string(b) + "]";
                for(int k = 0; k < core_feat::NUM; k++)
                {
                    snprintf(buf, sizeof(buf), "  %7.3f", used ? (double)sum[k] / (double)used : 0.0);
                    row += buf;
                }
                snprintf(buf, sizeof(buf), "  %10ld", (long)used);
                cout << row << buf << endl;
            }
        }
    }

    {//制約C フィルタの効き具合を側 x バケットごとに表示する(検証用)
        cout << endl;
#if USE_LEAF_FILTER
        cout << "leaf filter: ON  (制約C を満たさない局面は学習から外し、A も作らない)" << endl;
#else
        cout << "leaf filter: OFF (導入前と同じ挙動)" << endl;
#endif
        for(int s = 0; s < 2; s++)
        {
            const SideSpec &side = SIDES[s];
            for(int b = 0; b < 4; b++)
            {
                long long tot = 0, kept = 0;
                for(int n = 1; n <= gameNum; n++)
                    for(int i = side.bucket[b].begin; i < side.bucket[b].end; i = i + 2)
                        if(record[n][i] < INF) { tot++; if(leafC[n][i]) kept++; }
                cout << "  [" << side.name << ".bucket" << b << "] turn " << side.bucket[b].label
                     << "  " << kept << " / " << tot
                     << "  (" << (tot ? 100.0 * (double)kept / (double)tot : 0.0) << "%)" << endl;
            }
        }
#ifdef LEAF_FILTER_STAT_ONLY
        // 検証用: -DLEAF_FILTER_STAT_ONLY でビルドすると、上の内訳を出した時点で終了する。
        // 勾配降下法を回さずにフィルタの判定だけを確認できる。
        return 0;
#endif
    }

    int threadNum = omp_get_max_threads();//ランダム初期値の生成回数
	omp_set_num_threads(threadNum);
    cout << "number of thread = " << threadNum << endl;

	int best[2][4][pnum] = {};
	long double bestLoss[2][4] = {};

	for(int s = 0; s < 2; s++)
	{
		const SideSpec &side = SIDES[s];
		const int (*teacher)[34] = (s == 0) ? evaluatessec : evaluatesfir;
		for(int b = 0; b < 4; b++)
		{
			cout << endl;
			cout << "==================================================" << endl;
			cout << "[" << side.name << ".bucket" << b << "] turn " << side.bucket[b].label
			     << "  (for i = " << side.bucket[b].begin << "; i < " << side.bucket[b].end << "; i = i + 2)"
			     << "  teacher = " << side.teacher_name << ", restart = " << side.restart << endl;
			cout << "==================================================" << endl;

			run_gd(side.bucket[b].begin, side.bucket[b].end, side.restart,
			       teacher, threadNum, best[s][b], &bestLoss[s][b]);
		}
	}

	//ここから 8 回分のまとめ
	cout << endl;
	cout << "##################################################" << endl;
	cout << "#          全 8 回(2 側 x 4 バケット)の loss     #" << endl;
	cout << "##################################################" << endl;
	for(int s = 0; s < 2; s++)
	{
		for(int b = 0; b < 4; b++)
		{
			cout << SIDES[s].name << ".bucket" << b << " (turn " << SIDES[s].bucket[b].label << ") : ";
			for(int i = 0; i < pnum; i++) cout << best[s][b][i] << ",";
			cout << "loss = " << bestLoss[s][b] << endl;
		}
	}

	//ここから weights/verX_Y.txt 形式。ここから下をそのまま貼れば重みファイルになる。
	cout << endl;
	cout << "########## ここから下を weights/verX_Y.txt へ貼り付ける ##########" << endl;
	cout << endl;
	dump_core_weights_file(cout, WEIGHTS_NAME, best[0], best[1], bestLoss[0], bestLoss[1]);
	cout << endl;
	cout << "########## ここまで ##########" << endl;

	if(OUTPUT_WEIGHTS_PATH[0] != 0)
	{
		std::ofstream ofs(OUTPUT_WEIGHTS_PATH);
		if(ofs)
		{
			dump_core_weights_file(ofs, WEIGHTS_NAME, best[0], best[1], bestLoss[0], bestLoss[1]);
			cout << "wrote " << OUTPUT_WEIGHTS_PATH << endl;
		}
		else
		{
			cout << "failed to open " << OUTPUT_WEIGHTS_PATH << endl;
		}
	}

	return 0;
}