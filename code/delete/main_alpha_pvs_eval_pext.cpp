#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案7b(pext + 256 エントリテーブル)版ハーネス。基準は main_alpha_pvs.cpp(提案5まで実装済み)。
// AI は AIPlayerPVS を無変更で流用し、評価関数のみ _rp 版に差し替える
// (implementation-plan-eval-speedup.md §3.2、基準を提案1+2+3版→提案5版に読み替え)。
// ★要 BMI2。公平比較のため基準・7a も同フラグ(-march=native)で再ビルドして比較すること(§4)
//   g++ -std=c++17 -O2 -march=native -fopenmp code/main_alpha_pvs_eval_pext.cpp -o yonmoku_alpha_pvs_eval_pext
// ノード数計測: -DBENCH

#include "tt.hpp"
#include "ai_player_pvs.hpp"
#include "evaluate_alpha_pext.hpp"
using AI = AIPlayerPVS<int(*)(const Board&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();
	init_eval_tables();   // ★7b: pext 用テーブル構築(init_lines() の後)

	AI p1(10, evaluate_pointfir_cont_layer_intersection_rp);
	AI p2(10, evaluate_pointsec_cont_layer_intersection_rp);

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
