#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif
# include <omp.h>

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"

// 提案7a+7b+7c 統合版ハーネス。母体は main_alpha_pvs_eval_inc.cpp(7c)。
// BoardInc の増分 cnt[] を添字に 7b 型の単一テーブルを引く評価関数(_rit)を使う。
// 評価は BMI2 非依存(pext 不要)。基準は main_alpha_pvs.cpp(提案5まで)。
//   g++ -std=c++17 -O2 -fopenmp code/main_alpha_pvs_eval_inc_tbl.cpp -o yonmoku_alpha_pvs_eval_inc_tbl
// ノード数計測: -DBENCH / cnt 検証 assert 有効化: -DUSE_ASSERT

#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc.hpp"          // 無変更で流用
#include "evaluate_alpha_inc_tbl.hpp"     // ★7c → 統合版へ
using AI = AIPlayerPVSInc<int(*)(const BoardInc&, unsigned long long, unsigned long long, unsigned long long)>;

int main()
{
	init_lines();
	init_sq_lines();      // 7c と共通(BoardInc の増分維持に必要)
	init_cnt_tbl();       // ★統合版のテーブル構築(init_cnt_to_v() を置換)

	AI p1(60, evaluate_pointfir_cont_layer_intersection_rit);   // ★_ri → _rit
	AI p2(60, evaluate_pointsec_cont_layer_intersection_rit);

	auto st = chrono::system_clock::now();
	Game game(&p1, &p2, true, {{0, 0}, {3, 3}, {3, 3}, {0, 3}, {3, 0}, {1, 3}, {2, 3}, {1, 0}, {1, 0}, {1, 0}, {3, 0}, {0, 0}, {2, 3}, {1, 3}, {3, 3}, {1, 3}, {1, 3}, {3, 3}, {2, 3}, {2, 3}, {1, 1}, {0, 1}, {2, 0}, {2, 2}, {2, 2}, {2, 2}, {0, 1}, {0, 2}, {3, 2}, {0, 1}, {0, 2}, {3, 2}, {3, 2}, {3, 2}});  // 検証時は {} を基準版の hands 出力の先頭 n 手に差し替える(§5.1)
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
