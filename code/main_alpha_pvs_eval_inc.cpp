#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案7c(ライン充填数の増分更新)版ハーネス。基準は main_alpha_pvs.cpp(提案5まで実装済み)。
// AI は ai_player_pvs.hpp を BoardInc 化した AIPlayerPVSInc、評価関数は _ri 版
// (implementation-plan-eval-speedup.md §3.3、基準を提案1+2+3版→提案5版に読み替え)。
//   g++ -std=c++17 -O2 -fopenmp code/main_alpha_pvs_eval_inc.cpp -o yonmoku_alpha_pvs_eval_inc
// ノード数計測: -DBENCH / cnt 検証 assert 有効化: -DUSE_ASSERT

#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc.hpp"
#include "evaluate_alpha_inc.hpp"
using AI = AIPlayerPVSInc<int(*)(const BoardInc&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();
	init_sq_lines();      // ★7c: マス→ライン逆引きテーブル構築(init_lines() の後)
	init_cnt_to_v();      // ★7c: 充填数→count 値テーブル構築

	AI p1(10, evaluate_pointfir_cont_layer_intersection_ri);
	AI p2(10, evaluate_pointsec_cont_layer_intersection_ri);

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {});  // 検証時は {} を基準版の hands 出力の先頭 n 手に差し替える(§5.1)
	p1.set_game(&game);
	p2.set_game(&game);
	game.game();
	auto msec = chrono::duration_cast<chrono::milliseconds>(chrono::system_clock::now() - st);
	cout << "total: " << msec.count() / 1e3 << " sec" << endl;
#ifdef BENCH
	cout << "nodes: " << g_node_count << endl;
#endif
	return 0;
}
