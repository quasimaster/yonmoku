#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif

// main_core.cpp(既存版)の探索・評価をそのまま使う AI vs AI 自己対戦の計測ハーネス。
// 高速化版 bench_core2.cpp との速度比較・完全一致確認に使う(設計: docs/設計書/高速化/speedup-proposal-main-core.md §2)。
// bench_endgame_selfplay_w.cpp を母体に、次の 3 点を変えた。
//   1. 評価関数を EvalFnCore(evaluate_core.hpp)、重みを EvalWeightsCore にした(= main_core.cpp と同じ)
//   2. 第 4 引数で定跡の開始番号を指定できる(乱数状態は対局間で引き継がれるので、比較は同じ開始番号・同じ局数で行う)
//   3. 各局の root 評価値列(先手/後手)も出力する(置換表の変更で評価値が変わっていないかを diff で見るため)
//
//   引数: [対局数] [読み手数 level] [重みファイル("-" で組み込み既定値)] [定跡の開始番号]   既定 = 8 局 / level 10 / builtin / 0
//
// ビルド(比較は必ず同一フラグで):
//   g++ -std=c++17 -O2 -march=native -DBENCH code/bench_core.cpp  -o bench_core
//   g++ -std=c++17 -O2 -march=native -DBENCH code/bench_core2.cpp -o bench_core2
//   ./bench_core 3 10 - 2 > before.txt ; ./bench_core2 3 10 - 2 > after.txt
//   diff <(sed -E 's/ +[0-9.]+ sec//; /nodes=/d' before.txt) <(sed -E 's/ +[0-9.]+ sec//; /nodes=/d' after.txt)

#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"
#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc_id.hpp"
#include "evaluate_core.hpp"
using AI = AIPlayerPVSIncID<EvalFnCore>;
using Weights = EvalWeightsCore;
using EvalFnT = EvalFnCore;
static void init_tables() { init_lines(); init_sq_lines(); init_eval_tbl(); }

#include "bench_core_body.hpp"   // main()(bench_core.cpp / bench_core2.cpp で共通)
