#define NDEBUG          // ← すべての #include より前(assert 無効化)
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 速度比較ハーネス(実装計画書 §6)
//   g++ -std=c++17 -O2 -fopenmp -DUSE_TT=1 code/main_alpha_new.cpp -o yonmoku_alpha_tt
//   g++ -std=c++17 -O2 -fopenmp -DUSE_TT=0 code/main_alpha_new.cpp -o yonmoku_alpha_base
// ノード数計測: -DBENCH (USE_TT=1 のみ)、検証モード: -DTT_STRICT

#ifndef USE_TT
#define USE_TT 1
#endif

#if USE_TT
#include "tt.hpp"
#include "ai_player_tt.hpp"
using AI = AIPlayerTT<int(*)(const Board&)>;
#else
#include "ai_player.hpp"          // 既存のまま
using AI = AIPlayer<int(*)(const Board&)>;
#endif
#include "evaluate_alpha.hpp"

int main()
{
	init_lines();
	// rng.seed(20260707);           // 再現性確保(rng はグローバルなので main で seed できる)

	AI p1(10, evaluate_pointfir_cont_layer_intersection);
	AI p2(10, evaluate_pointsec_cont_layer_intersection);
	// set_random は呼ばない(= 0、常に最善手)

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {});  // main_alpha.cpp と同じ初手列
	p1.set_game(&game);
	p2.set_game(&game);
	game.game();
	auto msec = chrono::duration_cast<chrono::milliseconds>(chrono::system_clock::now() - st);
	cout << "total: " << msec.count() / 1e3 << " sec" << endl;
#if defined(BENCH) && USE_TT
	cout << "nodes: " << g_node_count << endl;
#endif
	return 0;
}
