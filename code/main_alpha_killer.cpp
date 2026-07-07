#define NDEBUG          // ← すべての #include より前(assert 無効化)
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案4(killer/history)版ハーネス。基準は main_alpha_tt_leaf_array.cpp
//   g++ -std=c++17 -O2 -fopenmp code/main_alpha_killer.cpp -o yonmoku_alpha_killer
// ノード数計測: -DBENCH / 3手読み温存版: -DUSE_DEEP_ORDER=1

#include "tt.hpp"
#include "ai_player_killer.hpp"
#include "evaluate_alpha_leaf.hpp"
using AI = AIPlayerKiller<int(*)(const Board&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();

	AI p1(10, evaluate_pointfir_cont_layer_intersection_r);
	AI p2(10, evaluate_pointsec_cont_layer_intersection_r);

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {{3,3}});  // 検証時は {} を基準版の hands 出力の先頭 n 手に差し替える(§5.1)
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
