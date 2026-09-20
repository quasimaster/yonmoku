#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif

// main_core2.cpp(高速化版)の探索・評価をそのまま使う AI vs AI 自己対戦の計測ハーネス。
// 既存版 bench_core.cpp と同一の本体(bench_core_body.hpp)を使い、include と型名だけが違う。
//
//   引数: [対局数] [読み手数 level] [重みファイル("-" で組み込み既定値)] [定跡の開始番号]
//
// 高速化項目の切替(すべて既定 ON。0 にすると流用元と同じ処理になる):
//   -DUSE_EVALSEL=0   葉評価の ±2 ライン抽出を無効化
//   -DUSE_LAZYSORT=0  手順の遅延選択を無効化(std::sort に戻す)
//   -DUSE_FIXCNT=0    cnt の向き固定を無効化(ニブル交換 SWAR に戻す)
//   -DUSE_TT_BUCKET=1 置換表のバケット化を無効化(1 way に戻す)
// 4 つとも無効にしたビルドは bench_core.cpp とノード数・着手列・評価値が完全に一致する。
//
//   g++ -std=c++17 -O2 -march=native -DBENCH code/bench_core2.cpp -o bench_core2

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
#include "tt2.hpp"
#include "board_inc2.hpp"
#include "ai_player_pvs_inc_id2.hpp"
#include "evaluate_core2.hpp"
using AI = AIPlayerPVSIncID2<EvalFnCore2>;
using Weights = EvalWeightsCore2;
using EvalFnT = EvalFnCore2;
static void init_tables() { init_lines(); init_sq_lines(); init_eval_tbl2(); }

#include "bench_core_body.hpp"   // main()(bench_core.cpp / bench_core2.cpp で共通)
