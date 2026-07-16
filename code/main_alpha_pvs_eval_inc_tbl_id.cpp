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

	AI p1(10, evaluate_pointfir_cont_layer_intersection_rit);   // ★_ri → _rit
	AI p2(10, evaluate_pointsec_cont_layer_intersection_rit);

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
