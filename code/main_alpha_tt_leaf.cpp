#define NDEBUG          // ← すべての #include より前(assert 無効化)
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案2(葉 reach 再計算排除)版ハーネス。基準は main_alpha_tt.cpp (-DUSE_TT=1)
//   g++ -std=c++17 -O2 -fopenmp code/main_alpha_tt_leaf.cpp -o yonmoku_alpha_tt_leaf
// ノード数計測: -DBENCH

#include "tt.hpp"
#include "ai_player_tt_leaf.hpp"
#include "evaluate_alpha_leaf.hpp"
using AI = AIPlayerTTLeaf<int(*)(const Board&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();
	// rng.seed(20260707);           // 再現性確保(rng はグローバルなので main で seed できる)

	AI p1(10, evaluate_pointfir_cont_layer_intersection_r);
	AI p2(10, evaluate_pointsec_cont_layer_intersection_r);
	// set_random は呼ばない(= 0、常に最善手)

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {});  // main_alpha_tt.cpp と同一
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
