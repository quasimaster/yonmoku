#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif

// ★main_core.cpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md、計測: docs/実行結果/benchmark-results-main-core-speedup.md)。
// 流用元 main_core.cpp との差分は include / using / 型名 / init 呼び出しだけで、対局ループ・自己対戦・出力書式は完全に同一。
//   tt.hpp → tt2.hpp(置換表の 4 way バケット化)               USE_TT_BUCKET(既定 4、1 で流用元と同一)
//   board_inc.hpp → board_inc2.hpp(cnt の向き固定)              USE_FIXCNT  (既定 1、0 で流用元と同一)
//   ai_player_pvs_inc_id.hpp → ai_player_pvs_inc_id2.hpp(手順の遅延選択)  USE_LAZYSORT(既定 1、0 で流用元と同一)
//   evaluate_core.hpp → evaluate_core2.hpp(葉評価の ±2 ライン抽出)        USE_EVALSEL (既定 1、0 で流用元と同一)
// USE_EVALSEL / USE_LAZYSORT / USE_FIXCNT は評価値・探索ノード数を一切変えない。USE_TT_BUCKET は置換表の中身が変わるので
// ノード数は変わる(root 評価値・最善手集合は実測 606 手番で不変。設計書 §9)。
// 速度比較は code/bench_core.cpp(既存版)と code/bench_core2.cpp(本版)で行う。
//
// 以下、流用元のコメント:
// main_alpha_pvs_eval_inc_tbl_id_w.cpp に「核 2 マスの全状態」の評価項(6 本 / バケット)を足した版。
// 設計: docs/設計書/評価関数パラメータ/investigation-new-eval-features.md §2.6 D
//
// 流用元 main_alpha_pvs_eval_inc_tbl_id_w.cpp との差分は次の 3 点だけ。
// 対局ループ・教師データ自己対戦・出力書式は完全に同一。
//   1. include を evaluate_core.hpp に差し替え(既存評価 + 核の項)
//   2. using AI を AIPlayerPVSIncID<EvalFnCore> に、重みを EvalWeightsCore に差し替え
//   3. --weights は version 1(既存。core = 0 として読む)と version 2(core 付き)の両方を受け付ける
// core が全部 0 のモデル(--weights 省略時の組み込み既定値 / version 1 のファイル)では、
// 流用元と 1 ノードも変わらない。core 付きの重みは MachineLearning/main_gd_core.cpp で学習する。
//
// ■ 教師データ自己対戦の出力先
//   流用元と同じ /yonmoku/esc/*_ver6_esc_thread*.csv のまま(自己対戦部は流用元どおり既定では実行されない)。
//   core 付きモデルで教師データを取るときは、既存データを上書きしないよう出力名を変えてから有効にすること。

// ===== 最終盤の厳密評価(段パリティ規則 R2 + ゲート付き厳密打ち切り)=====
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md
//   USE_ENDGAME_R2  : turn>=60 の葉評価を R0 → R2 に差し替え(ヒューリスティックの精度改善)
//   USE_ENDGAME_CUT : turn>=59 で「証明可能に厳密」な局面を確定値で即 return し部分木を刈る
// どちらも -DUSE_ENDGAME_R2=0 -DUSE_ENDGAME_CUT=0 で従来と完全同一の挙動に戻せる。
#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

//   g++ -std=c++17 -O2 -march=native -fopenmp code/main_core2.cpp -o main_core2      ★-march=native 推奨(popcount 等の命令化。-10 %)
//   実行時にモデルを差し替える: ./main_core2 --weights weights/core/verX_Y.txt   (version 1 = weights/alpha/ / version 2 = weights/core/ どちらも可)
// ノード数計測: -DBENCH / cnt 検証 assert 有効化: -DUSE_ASSERT / 最終盤打ち切りの自己検査: -DEG_SELFCHECK=1

#include "tt2.hpp"                        // ★置換表(4 way バケット)
#include "board_inc2.hpp"                 // ★BoardInc2(cnt 向き固定)
#include "ai_player_pvs_inc_id2.hpp"      // ★反復深化版 + 手順の遅延選択
#include "evaluate_core2.hpp"             // ★既存評価(±2 ライン抽出版) + 核 2 マスの全状態
using AI = AIPlayerPVSIncID2<EvalFnCore2>;

// ===== 定跡(重複なし初手列)の読み込み =====
// unique_opening/gen_unique_openings.cpp が出力するテキストを実行時に読む。
//   形式: 1 行 1 手順で "    {{0,0}, {0,0}, {0,0}, {0,1}}," (手数は 4/5/6 手のいずれでも可)
// 実行ディレクトリが読めない場合に備えて候補パスを順に試す。
static vector<vector<pair<int, int> > > load_openings(const string& rel_path)
{
	static const char* prefix[] = {"", "../", "../../"};
	ifstream ifs;
	string used;
	for(const char* p : prefix)
	{
		used = string(p) + rel_path;
		ifs.open(used);
		if(ifs) break;
		ifs.clear();
	}
	if(!ifs)
	{
		cerr << "openings file not found: " << rel_path << endl;
		return {};
	}

	vector<vector<pair<int, int> > > openings;
	string line;
	while(getline(ifs, line))
	{
		size_t head = line.find_first_not_of(" \t");
		if(head == string::npos || line.compare(head, 2, "{{") != 0) continue;   // 宣言行 / "};" を読み飛ばす

		vector<int> nums;                                 // 行中の整数を全て拾う(= {x,y} の並び)
		for(size_t i = head; i < line.size(); )
		{
			if(isdigit((unsigned char)line[i]))
			{
				int v = 0;
				while(i < line.size() && isdigit((unsigned char)line[i])) v = v * 10 + (line[i++] - '0');
				nums.push_back(v);
			}
			else i++;
		}
		if(nums.empty() || nums.size() % 2 != 0)
		{
			cerr << "skip malformed opening line: " << line << endl;
			continue;
		}

		vector<pair<int, int> > op;
		bool ok = true;
		for(size_t i = 0; i < nums.size(); i += 2)
		{
			if(nums[i] < 0 || nums[i] >= SIZE || nums[i + 1] < 0 || nums[i + 1] >= SIZE) { ok = false; break; }
			op.emplace_back(nums[i], nums[i + 1]);
		}
		if(!ok)
		{
			cerr << "skip out-of-range opening line: " << line << endl;
			continue;
		}
		openings.push_back(move(op));
	}
	cout << "openings loaded: " << openings.size() << " from " << used << endl;
	return openings;
}

// ★使用する評価関数の重み。--weights が無ければ組み込み既定値(ver7.2 + core = 0)。
static EvalWeightsCore2 g_loaded;
static const EvalWeightsCore2* g_weights = nullptr;

int main(int argc, char** argv)
{
	init_lines();
	init_sq_lines();      // 7c と共通(BoardInc の増分維持に必要)
	init_eval_tbl2();     // ★flag_tbl + flag_tbl_sw(ニブル交換済み)。重み表はモデル側が持つ

	// ===== 重みモデルの決定(設計書 §2.4)=====
	// 読み込みに失敗したら組み込み既定値へ戻さずに終了する。
	// どちらのモデルで教師データを取ったのか分からなくなる事故を防ぐため。
	g_weights = &EvalWeightsCore2::builtin();
	for(int i = 1; i < argc; i++)
	{
		if(string(argv[i]) == "--weights" && i + 1 < argc)
		{
			string err;
			if(!g_loaded.load(argv[++i], &err)) { cerr << "weights error: " << err << endl; return 1; }
			g_weights = &g_loaded;
		}
		else { cerr << "usage: " << argv[0] << " [--weights <path>]" << endl; return 2; }
	}
	cout << "weights: " << g_weights->base.name
	     << (g_weights == &EvalWeightsCore2::builtin() ? " (builtin)" : " (file)")
	     << (g_weights->has_core() ? " core: on" : " core: all 0 (= 既存評価と同一)") << endl;

	// ===== 人間 vs AI 対局(undo 機能付き)=====
	// 人間の手番で範囲外の座標(例 "100 100" や "-1 -1")を入力すると、
	// 直前の「AI 手 + 自分の手」を巻き戻して打ち直せる(設計: docs/設計書/implementation-plan-undo.md)。
	AI p1(10, EvalFnCore2{g_weights, false});   // 先手 = AI
	AI p2(10, EvalFnCore2{g_weights, true });   // 後手 = AI
	HumanPlayer human;                     // 後手 = 人間(undo 対応)
	//   先手を人間にしたい場合は下の Game を  Game game(&human, &p1, true, {});  に差し替える

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {});  // AI(先手) vs 人間(後手)
	p1.set_game(&game);                // set_game は AI 側のみ必要(HumanPlayer は不要)
	p2.set_game(&game);                // set_game は AI 側のみ必要(HumanPlayer は不要)
	game.game();                       // ★対局開始(人間手番で範囲外座標 → 一手戻る)連続で試合をする場合はここをコメントアウトする
	auto msec = chrono::duration_cast<chrono::milliseconds>(chrono::system_clock::now() - st);
	cout << "total: " << msec.count() / 1e3 << " sec" << endl;
#ifdef BENCH
	cout << "nodes: " << g_node_count << endl;
#endif
	return 0;   // 人間対局後はここで終了(以降の教師データ自己対戦は実行しない)連続で試合をする場合はここをコメントアウトする

	// ===== ここから機械学習の教師データ取得用の自己対戦(main_alpha.cpp より移植) =====
	//   移植時の変更点: AIPlayer → AI、評価関数を _rit 版に置換(F が BoardInc を取るため)
	int cnt[3] = {};

	// 定跡ファイルごとの手順数(対称性で重複を除いた後の通り数):
	//   unique_opening/unique_openings_4.txt : 4 手  →   2,925 通り
	//   unique_opening/unique_openings_5.txt : 5 手  →  19,421 通り
	//   unique_opening/unique_openings_6.txt : 6 手  → 129,018 通り
	//   (unique_openings.txt は _4.txt と同一内容。上記は各ファイルの "{{...}}" 行数 = load_openings が返す要素数)
	// 初手は「全通り(4^6 = 4096 通りの 3 手)」ではなく、対称性で重複を除いた定跡ファイルから取る。
	const vector<vector<pair<int, int> > > openings = load_openings("unique_opening/unique_openings_4.txt");
	if(openings.empty())
	{
		cerr << "no openings; abort self-play" << endl;
		return 1;
	}
	static const int PASSES = 4;                      // 定跡集合を何巡するか(ランダム性があるので巡ごとに棋譜は変わる)
	const int N = (int)openings.size() * PASSES;      // 1 スレッドあたりの対局数

	cout << "max_threads : " <<  omp_get_max_threads() << endl;
	static const int setting = 8;//使用するスレッド数
	omp_set_num_threads(setting);

	std::string output_first[setting];
	std::string output_second[setting];
	std::string output_records[setting];

	std::ofstream ofs_first[setting];
	std::ofstream ofs_second[setting];
	std::ofstream ofs_records[setting];

	for(int i = 0; i < setting; i++){
		output_first[i] = "/yonmoku/esc/first_evaluate_ver6_esc_thread" + std::to_string(i) + ".csv";
		output_second[i] = "/yonmoku/esc/second_evaluate_ver6_esc_thread" + std::to_string(i) + ".csv";
		output_records[i] = "/yonmoku/esc/record_ver6_esc_thread" + std::to_string(i) + ".csv";
	}
	for(int i = 0; i < setting; i++){
		ofs_first[i].open(output_first[i]);
		ofs_second[i].open(output_second[i]);
		ofs_records[i].open(output_records[i]);
	}

	std::string log;
	std::ofstream ofs_log;

	log = "/yonmoku/esc/log.csv";
	ofs_log.open(log);

	static const bool display = false;//表示の変更
	int gameNum[setting];

	static const int start_num[setting] = {0,0,0,0,0,0,0,0};
	for(int i = 0; i < setting; i++){
		gameNum[i] = start_num[i];
	}
	int start_sum = 0;
	for(int i = 0; i < setting; i++){
		start_sum += start_num[i];
	}
	# pragma omp parallel private(rng)
	{
		int thread = omp_get_thread_num();
		for(int t = start_num[thread]; t < N; t++)
		{
			AI p1(8, EvalFnCore2{g_weights, false});
			AI p2(8, EvalFnCore2{g_weights, true });
			p1.set_random(15);
			p2.set_random(15);//一部ランダム

			// cout << "Game #" << t  << endl;
			Game game(&p1, &p2, display, openings[t % (int)openings.size()]);   // ★定跡ファイルの手順を初手に使う
			p1.set_game(&game);
        	p2.set_game(&game);
			enum Color r = game.game();
			cnt[r]++;
			gameNum[thread]++;
			cout << "thread = " << thread << endl;
			cout << "Black : " << cnt[Color::Black] << endl;
			cout << "White : " << cnt[Color::White] << endl;
			cout << " Draw : " << cnt[Color::Draw] << endl;
			cout << "each thread ";
			for(int i = 0; i < setting; i++){
				cout << gameNum[i] << ",";
			}
			cout << "times game have finished" << endl;
			cout << (cnt[Color::Black] + cnt[Color::White] + cnt[Color::Draw] + start_sum) * 100 / (double)(N * setting) << " % has finished" << endl;
			for(int i = 0; i < setting; i++){
				ofs_log << gameNum[i] << ",";
			}
			ofs_log << std::endl;
			for(int i = 1; i < 33; i++)
			{
				ofs_first[thread] << game.evaluatesfir_tmp[i] << ",";
			}
			ofs_first[thread] << std::endl;
			for(int i = 1; i < 33; i++)
			{
				ofs_second[thread] << game.evaluatessec_tmp[i] << ",";
			}
			ofs_second[thread] << std::endl;
			for(int i = 0; i < 64; i++)
			{
				ofs_records[thread] << game.record_tmp[i] << ",";
			}
			ofs_records[thread] << std::endl;
			// #pragma omp barrier
		}
	}
	return 0;
}
