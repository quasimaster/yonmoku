#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案1後半(反復深化)版ハーネス。母体は main_alpha_pvs_eval_inc_tbl.cpp(7a+7b+7c 統合版)。
// AI を AIPlayerPVSIncID(root 反復深化)に差し替えただけで、評価・盤面・TT は流用元と同一。
//   g++ -std=c++17 -O2 -fopenmp            code/main_alpha_pvs_eval_inc_tbl_id.cpp -o yonmoku_alpha_id
//   g++ -std=c++17 -O2 -fopenmp -DUSE_ID=0 code/main_alpha_pvs_eval_inc_tbl_id.cpp -o yonmoku_alpha_base  (現行相当)
// ノード数計測: -DBENCH / cnt 検証 assert 有効化: -DUSE_ASSERT

#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc_id.hpp"       // ★反復深化版(USE_ID で有/無切替)
#include "evaluate_alpha_inc_tbl.hpp"     // ★7c → 統合版へ
using AI = AIPlayerPVSIncID<int(*)(const BoardInc&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();
	init_sq_lines();      // 7c と共通(BoardInc の増分維持に必要)
	init_cnt_tbl();       // ★統合版のテーブル構築(init_cnt_to_v() を置換)

	// ===== 人間 vs AI 対局(undo 機能付き)=====
	// 人間の手番で範囲外の座標(例 "100 100" や "-1 -1")を入力すると、
	// 直前の「AI 手 + 自分の手」を巻き戻して打ち直せる(設計: docs/設計書/implementation-plan-undo.md)。
	AI p1(10, evaluate_pointfir_cont_layer_intersection_rit);   // 先手 = AI
	HumanPlayer human;                                          // 後手 = 人間(undo 対応)
	//   先手を人間にしたい場合は下の Game を  Game game(&human, &p1, true, {});  に差し替える

	auto st = chrono::system_clock::now();
	Game game(&p1, &human, true, {});  // AI(先手) vs 人間(後手)
	p1.set_game(&game);                // set_game は AI 側のみ必要(HumanPlayer は不要)
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
	static const int N = 4096;//<=100000 4096 8192

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
	static const int start[4] = {0, 1, 2, 3};
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
			AI p1(8, evaluate_pointfir_cont_layer_intersection_rit);
			AI p2(8, evaluate_pointsec_cont_layer_intersection_rit);
			p1.set_random(15);
			p2.set_random(15);//一部ランダム

			// cout << "Game #" << t  << endl;
			Game game(&p1, &p2, display, {{start[t % 4], start[(t / 4) % 4]}, {start[(t / 16) % 4], start[(t / 64) % 4]},
											{start[(t / 256) % 4], start[(t / 1024) % 4]}});
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
