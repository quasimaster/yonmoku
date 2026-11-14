#include <stdlib.h>
#include <omp.h>

#include "../code/common.hpp"
#include "../code/board.hpp"
#include "evaluate_gd_alpha.hpp"
#include "console_utf8.hpp"

int evaluatesfir[100000][34] = {};
int evaluatessec[100000][34] = {};
int record[100001][65] = {};

const int pnum = 29;
int A[100001][64][pnum+1];

// main_gd_alpha.cpp では 160〜163 行目のコメントアウトを 1 つずつ切り替えて
// 4 つの手数範囲それぞれについて勾配降下法を回していた。
// このファイルはその 4 範囲を 1 回の実行で順番に回し、結果をまとめて出力する。
// 勾配降下法の処理そのものは main_gd_alpha.cpp と同一。
// 教師データの読み込みと特徴量行列 A の構築は範囲に依存しないので 1 回だけ行う。
struct RangeSpec
{
	const char *label;
	int begin;  // for(int i = begin; i < end; i = i + 2) の begin
	int end;    // 同上 end
};
static const int rangeNum = 4;
static const RangeSpec ranges[rangeNum] =
{
	{"4~17",   3, 17},
	{"18~31", 17, 31},
	{"32~45", 31, 45},
	{"46~59", 45, 59},
};

// bestOne を code/evaluate_alpha_inc_tbl.hpp へ転記しやすいように
// 各評価テーブルの行フォーマットへ整形して項目ごとに出力する。
// 添字と意味の対応は特徴量構築部(pb = ps[0] ... pqg = ps[28])と同一。
static void print_for_hpp(const int bestOne[])
{
	const int pb = bestOne[0],  pc = bestOne[1],  pd = bestOne[2],  pe = bestOne[3];   //基礎点
	const int pg = bestOne[4],  ph = bestOne[5],  pi = bestOne[6];                     //layer_me
	const int pj = bestOne[7],  pk = bestOne[8],  pl = bestOne[9];                     //layer_you
	const int pm = bestOne[10], pn = bestOne[11], pr = bestOne[12], pt = bestOne[13];  //intersection
	const int po = bestOne[14];                                                        //continuous
	const int ppa = bestOne[15], ppb = bestOne[16], ppc = bestOne[17], ppd = bestOne[18]; //makeT me
	const int pqa = bestOne[19], pqb = bestOne[20], pqc = bestOne[21], pqd = bestOne[22]; //makeT you
	const int ppe = bestOne[23], ppf = bestOne[24], ppg = bestOne[25]; //conti makeT me
	const int pqe = bestOne[26], pqf = bestOne[27], pqg = bestOne[28]; //conti makeT you

	cout << "stdweight_fir: " << 0 << "," << pb << "," << pc << "," << 0 << "," << pd << "," << pe << "," << 0 << "," << endl;
	cout << "maketweight: " << ppa << "," << ppb << "," << ppc << "," << ppd << "," << pqa << "," << pqb << "," << pqc << "," << pqd << "," << endl;
	cout << "conti_maketweight: " << ppe << "," << ppf << "," << ppg << "," << pqe << "," << pqf << "," << pqg << "," << endl;
	cout << "layer_me: " << pg << "," << ph << "," << pi << "," << endl;
	cout << "layer_you: " << pj << "," << pk << "," << pl << "," << endl;
	cout << "intersection: " << pm << "," << pn << "," << pr << "," << pt << "," << endl;
	cout << "continuous: " << po << "," << endl;
}

int main()
{
	//コンソールの出力コードページを UTF-8 に合わせる(日本語の文字化け対策)
	enable_utf8_console();
	init_lines();

    std::string input_first_evaluate = "/yonmoku/teacher/first_evaluate_ver8_2.csv";
	std::string input_second_evaluate = "/yonmoku/teacher/second_evaluate_ver8_2.csv";
	std::string input_record = "/yonmoku/teacher/record_ver8_2.csv";

	std::ifstream ifs_first_evaluate (input_first_evaluate);
	std::ifstream ifs_second_evaluate (input_second_evaluate);
	std::ifstream ifs_record (input_record);

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

	std::string outputFile = "/yonmoku/feature.csv";
    std::ofstream ofs_outputFile(outputFile);

	static const int gameNum = 93600;
	//Aに各盤面のパラメータの出現数を入れる
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

                for(int p = 0; p <= pnum; p++)
                {
                    int ps[pnum]; //= {-60, -56, -16, 16, 56, 60, 30, 140, 11, 64, 16};//初期設定パラメータ
                    for(int i = 0; i < pnum; i++)
                    {
                        ps[i] = 0;
                    }
                    if (p < pnum) ps[p] = 1;
                    pb = ps[0], pc = ps[1], pd = ps[2], pe = ps[3];//基礎点
					pg = ps[4], ph = ps[5], pi = ps[6];//layer_me
					pj = ps[7], pk = ps[8], pl = ps[9];//leyer_you
					pm = ps[10], pn = ps[11], pr = ps[12], pt = ps[13];//intersection
					po = ps[14];//continuous
                    //pp = ps[17], pq = ps[18];//make T
					ppa = ps[15], ppb = ps[16], ppc = ps[17], ppd = ps[18];//nonfloat_makeT me
					pqa = ps[19], pqb = ps[20], pqc = ps[21], pqd = ps[22];//nonfloat_makeT you
					ppe = ps[23], ppf = ps[24], ppg = ps[25];//float_make me
					pqe = ps[26], pqf = ps[27], pqg = ps[28];//float_make you
                    A[n][i][p] = evaluate_pointfir_cont_layer_intersection(c);
                }
                //定数項の影響を除く
                for(int p = 0; p < pnum; p++) A[n][i][p] -= A[n][i][pnum];

            }
        }
    }

	//int parameter[pnum]= {-77,-65,-28,15,68,35,117,634,83,239,294,148,375,-163,928,0,599,346,2,69,19,7,39,34,15};


    int threadNum = omp_get_max_threads();//ランダム初期値の生成回数
	// threadNum = 1;
	omp_set_num_threads(threadNum);
    cout << "number of thread = " << threadNum << endl;

	// 4 範囲分の結果を保存しておき、最後にまとめて表示する。
	int bestOneAll[rangeNum][pnum + 1] = {};
	long double bestOneLossAll[rangeNum] = {};

	//ここから 4 範囲を順番に回す
	for(int r = 0; r < rangeNum; r++)
	{
	const int rangeBegin = ranges[r].begin;
	const int rangeEnd   = ranges[r].end;

	cout << endl;
	cout << "==================================================" << endl;
	cout << "range[" << r << "] = " << ranges[r].label
	     << "  (for i = " << rangeBegin << "; i < " << rangeEnd << "; i = i + 2)" << endl;
	cout << "==================================================" << endl;

	long double bestloss[threadNum][pnum + 1];
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
		for(int i = 0; i < pnum; i++)cout << random_parameter[i] << ",";
		cout << endl;

		for(int t = 0; t < 30; t++)
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
					// main_gd_alpha.cpp では下記 4 つのうち 1 つだけを有効にしていた箇所。
					// ここでは ranges[r] で範囲を切り替える。
					// for(int i = 3; i < 17; i = i + 2)//4~17
					// for(int i = 17; i < 31; i = i + 2)//18~31
					// for(int i = 31; i < 45; i = i + 2)//32~45
					// for(int i = 45; i < 59; i = i + 2)//46~59
					//for(int i = 43; i < 53; i = i + 2)//44~53
					for(int i = rangeBegin; i < rangeEnd; i = i + 2)
					{
						if(record[t][i] < INF)
						{
							//if((i % 2 == 1) && (evaluatessec[t][(i - 1) >> 1] > -INF) && (evaluatessec[t][(i - 1) >> 1] < INF))
							if((evaluatessec[t][(i - 1) >> 1] > -INF) && (evaluatessec[t][(i - 1) >> 1] < INF))
							{
								//int training_old = evaluate_pointfir_layer_intersection(c);
								int training = A[t][i][pnum];
								//for(int p = 0; p < pnum; p++) training += parameter[p] * A[t][i][p];
								for(int p = 0; p < pnum; p++) training += random_parameter[p] * A[t][i][p];
								//assert(training == training_old);
								long double p;
								long double q;

								if(evaluatessec[t][(i - 1)/2] < -1840) p = 0.99;
								else if(evaluatessec[t][(i - 1)/2] > 1840) p = 0.01;
								else p = 1 - 1/(1 + exp((long double)-(evaluatessec[t][(i - 1)/2])/400));
								if(training < -1840) q = 0.01;
								else if(training > 1840) q = 0.99;
								else q = 1/(1 + exp((long double)-(training)/400));
								/*long double p = 1 - 1/(1 + exp((long double)-(evaluatessec[t][(i - 1)/2] + 112)/200));
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
	float bestOneLoss;
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

	// 上の一行羅列に加え、code/evaluate_alpha_inc_tbl.hpp へ転記しやすいように
	// bestOne[0..28] を各評価テーブルの行フォーマットへ整形して項目ごとに出力する。
	cout << endl;
	cout << "--- range " << ranges[r].label << " : code/evaluate_alpha_inc_tbl.hpp 転記用 ---" << endl;
	print_for_hpp(bestOne);

	// 最後のまとめ表示用に保存する。
	for(int i = 0; i <= pnum; i++) bestOneAll[r][i] = bestOne[i];
	bestOneLossAll[r] = bestOneLoss;

	}//range ループここまで

	//ここから 4 範囲分のまとめ
	cout << endl;
	cout << "##################################################" << endl;
	cout << "#            全 4 範囲の結果まとめ               #" << endl;
	cout << "##################################################" << endl;
	for(int r = 0; r < rangeNum; r++)
	{
		cout << "range " << ranges[r].label << " : best thread = " << bestOneAll[r][pnum] << ",  ";
		for(int i = 0; i < pnum; i++) cout << bestOneAll[r][i] << ",";
		cout << "loss = " << bestOneLossAll[r] << endl;
	}
	for(int r = 0; r < rangeNum; r++)
	{
		cout << endl;
		cout << "--- range " << ranges[r].label << " : code/evaluate_alpha_inc_tbl.hpp 転記用 ---" << endl;
		print_for_hpp(bestOneAll[r]);
	}

	return 0;
}
