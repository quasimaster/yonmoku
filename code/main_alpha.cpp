#define NDEBUG          // ← すべての #include より前（assert 無効化）
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"
#include "ai_player.hpp"
#include "evaluate_alpha.hpp"

int main()
{
	init_lines();

	HumanPlayer H;
	AIPlayer p1(8, evaluate_pointfir_cont_layer_intersection);
	AIPlayer p2(8, evaluate_pointsec_cont_layer_intersection);
	AIPlayer p3(6, evaluate_random);//全ランダム
	AIPlayer p4(6, evaluate_random);//全ランダム
	// p1.set_random(10);
	// p2.set_random(10);//一部ランダム
	Game game(&H, &p2, true, {{0,0}, {3,3}, {3,0},{0,3},{0,0},{3,3}});//ゲーム設定
	p1.set_game(&game);
	p2.set_game(&game);
	game.game();//連続で試合をする場合はここをコメントアウトする
	return 0;//連続で試合をする場合はここをコメントアウトする
	int cnt[3] = {};
	static const int N = 4096;//<=100000 4096 8192

	//return 0;

	// std::string output_first_evaluate = "/yonmoku/first_evaluate_ver5_esc.csv";
	// std::string output_second_evaluate = "/yonmoku/second_evaluate_ver5_esc.csv";
	// std::string output_record= "/yonmoku/record_ver5_esc.csv";

	// std::ofstream ofs_first_evaluate(output_first_evaluate);
	// std::ofstream ofs_second_evaluate(output_second_evaluate);
	// std::ofstream ofs_record(output_record);

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


	static const int start_num[setting] = {4096,4096,4096,3920,4096,4096,4096,4096};
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
			AIPlayer p1(8, evaluate_pointfir_cont_layer_intersection);
			AIPlayer p2(8, evaluate_pointsec_cont_layer_intersection);
			p1.set_random(10);
			p2.set_random(10);//一部ランダム

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
	// for(int t = 0; t < N; t++)
	// {
	// 	//if(t % sparse == 1 || t == N || sparse == 1)
	// 	{
	// 		cout << "Game #" << t << endl;
	// 	}
	// 	Game game(&p1, &p2, display, {{start[t % 4], start[(t / 4) % 4]}, {start[(t / 16) % 4], start[(t / 64) % 4]},
	// 									{start[(t / 256) % 4], start[(t / 1024) % 4]}});
	// 	enum Color r = game.game();
	// 	cnt[r]++;
	// 	//if(t % sparse == 0 || t == N)
	// 	{
	// 		cout << "Black : " << cnt[Color::Black] << endl;
	// 		cout << "White : " << cnt[Color::White] << endl;
	// 		cout << " Draw : " << cnt[Color::Draw] << endl;
	// 	}
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_first_evaluate << evaluatesfir[t][i] << ",";
	// 		ofs_first_evaluate << game.evaluatesfir_tmp[i] << ",";
	// 	}
	// 	ofs_first_evaluate << std::endl;
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_second_evaluate << evaluatessec[t][i] << ",";
	// 		ofs_second_evaluate << game.evaluatessec_tmp[i] << ",";
	// 	}
	// 	ofs_second_evaluate << std::endl;
	// 	for(int i = 0; i < 64; i++)
	// 	{
	// 		//ofs_record << record[t][i] << ",";
	// 		ofs_record << game.record_tmp[i] << ",";
	// 	}
	// 	ofs_record << std::endl;
	// }

	// return 0;
	// //std::string output_csv_file_path = "/yonmoku/parameter2.csv";
	// //std::ofstream ofs_csv_file(output_csv_file_path );

	// for(int t = 1; t <= N; t++)
	// {
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_first_evaluate << evaluatesfir[t][i] << ",";
	// 		ofs_first_evaluate << game.evaluatesfir_tmp[i] << ",";
	// 	}
	// 	ofs_first_evaluate << std::endl;
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_second_evaluate << evaluatessec[t][i] << ",";
	// 		ofs_second_evaluate << game.evaluatessec_tmp[i] << ",";
	// 	}
	// 	ofs_second_evaluate << std::endl;
	// 	for(int i = 0; i < 64; i++)
	// 	{
	// 		//ofs_record << record[t][i] << ",";
	// 		ofs_record << game.record_tmp[i] << ",";
	// 	}
	// 	ofs_record << std::endl;
	// }

	return 0;
}
