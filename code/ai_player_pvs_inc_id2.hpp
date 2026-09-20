#pragma once

#include <climits>
#include <cstring>

#include "game.hpp"
#include "tt2.hpp"          // ★TranspositionTable2(N way バケット)
#include "board_inc2.hpp"   // ★BoardInc2(cnt 向き固定)

// ★ai_player_pvs_inc_id.hpp の高速化版(設計: docs/設計書/高速化/speedup-proposal-main-core.md §4.2 / §4.3 / §9.5)。
//   流用元との差分は次の 4 点だけ。探索アルゴリズム(αβ/PVS/killer/history/反復深化/最終盤打ち切り)は同一。
//   1. BoardInc → BoardInc2、TranspositionTable → TranspositionTable2(いずれも別ヘッダで切替可能)
//   2. [A]/[B]: USE_LAZYSORT=1 で「(score, bit) の std::sort」を「u64 キー(score<<6|sq)の遅延選択」に置換。
//      並び順は pair(score,bit) の降順と同一(キーは sq を含むので全て異なる)。βカットで早く抜けるほどソート分が浮く。
//   3. board_inc_consistent → board_inc2_consistent(assert 用)
//   4. struct 名を AIPlayerPVSIncID2 に変更
//   USE_LAZYSORT=0 / USE_FIXCNT=0 / USE_TT_BUCKET=1 のビルドは流用元とノード数まで完全一致する。
#ifndef USE_LAZYSORT
#define USE_LAZYSORT 1
#endif

// 探索が使う乱数(同点手の選択 / set_random によるランダム手)。既定はグローバル rng(common.hpp)。
// 複数スレッドで AI を回すプログラムは、include 前に thread_local な生成器を指すよう定義する
// (例: code/match_weights.cpp)。未定義なら従来と完全に同一。
#ifndef AI_RNG
#define AI_RNG rng
#endif

// 葉(level <= 0 の evaluate_func)を depth0 EXACT として格納するか。
// -DTT_STORE_LEAF=0 で無効化してベンチ比較できる(実装計画書 §4.4)
#ifndef TT_STORE_LEAF
#define TT_STORE_LEAF 1
#endif

// 提案4 A/B 用: 1 なら現行の4手読み事前ソートを温存(βカット時の killer/history 更新のみ追加)、
// 0(デフォルト)なら killer/history + 静的 move_order の安価な ordering に置換
// (実装計画書 implementation-plan-killer-history.md §3.4)
#ifndef USE_DEEP_ORDER
#define USE_DEEP_ORDER 0
#endif

// 提案5 A/B 用: 1(デフォルト)なら PVS(最初の手のみフルウィンドウ、以降 null window)、
// 0 なら全手フルウィンドウ
#ifndef USE_PVS
#define USE_PVS 1
#endif

// 提案1後半 A/B 用: 1(デフォルト)なら root 反復深化、
// 0 なら現行の1回きり探索(= ai_player_pvs_inc.hpp と同一挙動)
// (実装計画書 implementation-plan-iterative-deepening.md §1.4)
#ifndef USE_ID
#define USE_ID 1
#endif

// root 反復深化の最終読み深さ d(総読み手数 N = d + 1)を外から差し替えるためのフック。
// 既定の展開は従来のハードコード式と文字通り同一なので、既存ビルドの挙動は一切変わらない。
// Web 版(難易度プロファイル)だけが -DYON_DEPTH_TARGET=yon_depth_target で差し替える。
//   設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §2.4
#ifndef YON_DEPTH_TARGET
// #define YON_DEPTH_TARGET(turn, level) ((turn)>=37?25:(turn)>=29?11:(turn)>=21?9:(level)-1)//教師データ用ver7,シグモイド関数の係数は1840
#define YON_DEPTH_TARGET(turn, level) ((turn)>=35?27:(turn)>=27?11:(turn)>=19?9:(level)-1)//教師データ用ver8,シグモイド関数の係数は1840

#endif

// フェーズ2(最終盤のゲート付き厳密打ち切り)。
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md §3.3
//   0 = 現行と完全同一(追記は一切効かない)
//   1 = turn >= 59 で「R2 が厳密であると証明できる」局面を確定値で即 return し部分木を刈る
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 0
#endif

// Universal WDL solver: enabled by move count only, never by a board gate.
// Opt-in because WDL scores do not encode distance to mate.
#ifndef USE_ENDGAME_UNIVERSAL
#define USE_ENDGAME_UNIVERSAL 0
#endif
#ifndef ENDGAME_UNIVERSAL_MAX_EMPTY
#define ENDGAME_UNIVERSAL_MAX_EMPTY 10
#endif
#if USE_ENDGAME_UNIVERSAL
#include "endgame_universal.hpp"
static_assert(ENDGAME_UNIVERSAL_MAX_EMPTY >= 0 && ENDGAME_UNIVERSAL_MAX_EMPTY <= 12,
              "ENDGAME_UNIVERSAL_MAX_EMPTY must be between 0 and 12");
#ifndef ENDGAME_UNIVERSAL_EVALUATE
#define ENDGAME_UNIVERSAL_EVALUATE(b) endgame_universal::solve(b)
#endif
#endif

// フェーズ3(任意・既定 OFF)。turn=62 はゲートを通らなくても「勝敗を断定したときだけ」健全なので、
// 断定した場合に限り打ち切る(設計書 §3.5)。USE_ENDGAME_CUT=1 のときのみ意味を持つ。
#ifndef USE_ENDGAME_CUT62
#define USE_ENDGAME_CUT62 0
#endif

// 打ち切りで得た値を TT に入れるときの depth。
// 局面の真値(level に依存しない)なので、どの深さの probe からカットに使っても正しい。
#ifndef EG_TT_DEPTH
#define EG_TT_DEPTH 64
#endif

// 自己検査ビルド。打ち切り発火時に部分木を全読みして勝ち/引き分け/負けの 3 値を照合する
// (設計書 §5.3)。極めて遅くなるので検証専用。
#ifndef EG_SELFCHECK
#define EG_SELFCHECK 0
#endif

#if USE_ENDGAME_CUT
#include "endgame_exact.hpp"
#endif
#if EG_SELFCHECK
#include <cstdio>
#include <cstdlib>
inline thread_local long long g_eg_check_count = 0;   // 照合した打ち切り発火数
#endif

// 提案1後半(反復深化)版。ai_player_pvs_inc.hpp の AIPlayerPVSInc のコピーで、
// struct を AIPlayerPVSIncID に改名し、root(move())にのみ反復深化を実装したもの。
//   - evaluate_board(内部ノード)/ update_cut / メンバは流用元と完全同一(無変更)
//   - move() は「読み手数 N = 4, 6, …, level を 2 手ずつ深める」反復深化に置換
//     (§1.3: 評価関数の偶数手読み前提を厳守。evaluate_board 深さ d = N-1)
//   - 反復間で tt.new_search() を呼ばず、浅い反復の TT を深い反復が再利用(§1.2)
//   - USE_ID=0 で現行 ai_player_pvs_inc.hpp と完全同一挙動になる
// 評価関数 F は int(*)(const BoardInc&, ull, ull, ull)(evaluate_alpha_inc.hpp の _ri 版)
template<typename F>
struct AIPlayerPVSIncID2 : Player
{
	using Player::verbose;
	using Player::random;
	int level;
	F evaluate_func;
	Game* game = nullptr;
	TranspositionTable2 tt;   // インスタンス毎(スレッド間・プレイヤー間で共有しない)
	static const int MAX_PLY = 64;
	unsigned char killer[MAX_PLY][2];   // βカットを起こした手(マス番号)。未設定 = TT_NO_MOVE
	int history[64];                    // history[sq] += level * level(1 << 28 で飽和)
	AIPlayerPVSIncID2(int level, F evaluate_func, int tt_bits = 22) : level(level), evaluate_func(evaluate_func), tt(tt_bits) { assert(level >= 1); }

	void set_game(Game* g) { game = g; }

	// [C] βカットを起こした手 sq の killer / history 更新
	inline void update_cut(int sq, int level, int ply)
	{
		if (sq != killer[ply][0]) { killer[ply][1] = killer[ply][0]; killer[ply][0] = (unsigned char)sq; }
		history[sq] = min(history[sq] + level * level, 1 << 28);   // 飽和(手番リセット前の桁あふれ保険)
	}

	int evaluate_board(const BoardInc2 &board, int level, int alpha, int beta, int ply)
	{
#ifdef BENCH
		g_node_count++;
#endif
		assert(board_inc2_consistent(board));  // 7c: cnt の増分更新の妥当性検証(NDEBUG で消える)
		unsigned long long hand = board.b.valid_move();
		if (!hand) return 0;
		// ★turn を巻き上げ(旧 :103 / :117 / :121 の再計算を兼ねる)。
		//   board はこの間変化しないので挙動は不変で、popcount の呼び出し回数はむしろ減る。
		const int turn = board.b.turn();// turn number (the number of stones = turn - 1)

		//[1] probe
		const unsigned long long key = TranspositionTable2::hash(board.b);
		unsigned char tt_move = TT_NO_MOVE;
		if (const TTEntry* e = tt.probe(key))
		{
#ifdef TT_STRICT
			// 検証モード: ベースラインと root 評価値が完全一致するはずの条件のみでカット
			// (同一深さ・EXACT・窓内。ordering への利用もしない)
			if (e->depth == level && e->bound == TT_EXACT && alpha < e->value && e->value < beta) return e->value;
#else
			if (e->depth >= level)
			{
				if (e->bound == TT_EXACT) return e->value;
				if (e->bound == TT_LOWER && e->value >= beta)  return e->value;
				if (e->bound == TT_UPPER && e->value <= alpha) return e->value;
				if (e->bound == TT_LOWER) alpha = max(alpha, e->value);
				if (e->bound == TT_UPPER) beta  = min(beta,  e->value);
			}
			tt_move = e->best_move;    // 深さ不足でも ordering には使う
#endif
		}
		const int alpha_orig = alpha;   // bound 分類用に保存
#if USE_ENDGAME_UNIVERSAL
		if (65 - turn <= ENDGAME_UNIVERSAL_MAX_EMPTY)
		{
			const int ev = ENDGAME_UNIVERSAL_EVALUATE(board.b) * (INF - 100000);
			tt.store(key, ev, 64, TT_EXACT, TT_NO_MOVE);
			return ev;
		}
#endif

		{//reach (既存のまま。即勝ち/即負けの return は格納しない)
			const unsigned long long rMe_raw = Board::reach(board.b.Me);   // 提案2: スコープ外へ持ち上げ
			{
				const unsigned long long r = hand & rMe_raw;
				if (r) return INF - turn;
			}
			const unsigned long long rYou_raw = Board::reach(board.b.You); // 提案2: 名前を付けて保持
			{
				if (hand & rYou_raw) hand = hand & rYou_raw;
				else
				{
					// ここに来た時点で hand & rMe_raw == 0 かつ hand & rYou_raw == 0。
					// = 「即座に置けるマスの上には双方どちらのリーチも無い」= 研究の制約(C)。
					// 制約(C) が成立する唯一の位置なので、厳密打ち切りの挿入点もここ 1 点に限られる。
#if USE_ENDGAME_CUT
					if (turn >= 59)
					{
						const bool gated = endgame_gate(board, turn);
						// フェーズ3(既定 OFF): turn=62 はゲート無しでも「勝敗を断定したときだけ」健全。
						// 誤るとしても「決着を引き分けと言う」方向にしか誤らない(設計書 §3.5)。
						// turn=61 に広げてはならない(ゲート無しの 61 は誤断定 2.0% がある)。
						const bool sound62 = USE_ENDGAME_CUT62 && turn == 62;
						if (gated || sound62)
						{
							const int ev = endgame_value(board.b, turn, rMe_raw, rYou_raw);
							if (gated || ev != 0)   // ゲート不通過の turn=62 は断定したときだけ信じる
							{
#if EG_SELFCHECK
								{//打ち切りを使わない全読みと 勝ち/引き分け/負け の 3 値で照合(設計書 §5.3)
									const int truth = endgame_solve_exact(board.b);
									const int sign  = (ev > 0) - (ev < 0);
									if (sign != truth)
									{
										fprintf(stderr, "EG_SELFCHECK FAILED: turn=%d gated=%d ev=%d sign=%d truth=%d Me=%llu You=%llu\n",
										        turn, (int)gated, ev, sign, truth,
										        (unsigned long long)board.b.Me, (unsigned long long)board.b.You);
										abort();
									}
									g_eg_check_count++;
								}
#endif
								tt.store(key, ev, EG_TT_DEPTH, TT_EXACT, TT_NO_MOVE);
								return ev;         // 厳密値なので level に関係なく部分木を丸ごと刈る
							}
						}
					}
					// ゲート不通過 = 確定できない → 何も断定せず現行の経路へ落ちる
#endif
					if (level <= 0)
					{
						const int ev = evaluate_func(board, rMe_raw, rYou_raw, hand);  // 提案2: 再計算排除
#if TT_STORE_LEAF
						tt.store(key, ev, 0, TT_EXACT, TT_NO_MOVE);   //[2] 葉も depth0 で格納
#endif
						return ev;
					}
				}
				hand &= ~(rYou_raw >> SIZE * SIZE);
				if (!hand) return -(INF - (turn + 1));
			}
		}

		unsigned char best_move = TT_NO_MOVE;
		bool pv_done = false;   // ★PVS: フルウィンドウで探索済みの手があるか(§3.1)

		//[3] TT best_move を最初に試す(強制手絞り込み後の hand で合法性確認。フルウィンドウのまま)
		if (tt_move != TT_NO_MOVE && (hand >> tt_move & 1))
		{
			const unsigned long long bit = 1uLL << tt_move;
			BoardInc2 b = board.place_fast_clone(bit);
			int ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
			if (ev > alpha) { alpha = ev; best_move = tt_move; }
			pv_done = true;                          // ★PVS: 最初の手は探索済み
			if (alpha >= beta) update_cut(tt_move, level, ply);   //[C] TT move でのβカットも更新(提案4 §3.3)
			hand &= ~bit;
		}

		if (alpha < beta)
		{
#if USE_DEEP_ORDER
			if(level >= 8 && turn < 46 || level >= 10 && turn >= 46)//教師データ取得用
			{
				//4手読みパート
				array<pair<int, unsigned long long>, 16> dynamic;   // 提案3: vector → スタック固定長(合法手は最大16)
				int n = 0;                                          // 提案3: 要素数
				for (const unsigned long long mask: move_order)
				{
					unsigned long long h = hand & mask;
					hand ^= h;
					while (h)
					{
						const unsigned long long bit = h & -h;
						BoardInc2 b = board.place_fast_clone(bit);
						enum State r = Board::win(b.b.You);

						assert(r == State::Continue);
						int ev = -evaluate_board(b, 3 , -INF , INF, ply + 1);
						dynamic[n++] = make_pair(ev, bit);          // 提案3: push_back → 添字代入
						h ^= bit;
					}
				}
				sort(dynamic.begin(), dynamic.begin() + n, greater<pair<int, unsigned long long>>());  // 提案3: 降順(rbegin/rend と結果列一致)

				for(int i = 0; i < n; i++)                          // 提案3: dynamic.size() → n
				{
					const unsigned long long bit = dynamic[i].second;
					BoardInc2 b = board.place_fast_clone(bit);
					enum State r = Board::win(b.b.You);

					assert(r == State::Continue);
					int ev;
#if USE_PVS
					if (!pv_done)
					{
						ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);       // 最初の手: フル
					}
					else
					{
						ev = -evaluate_board(b, level - 1, -alpha - 1, -alpha, ply + 1);  // null window
						if (alpha < ev && ev < beta)
							ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);   // fail high → 再探索
					}
#else
					ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);           // 提案4版と同一
#endif
					pv_done = true;
					if (ev > alpha) { alpha = ev; best_move = (unsigned char)__builtin_ctzll(bit); }
					if (alpha >= beta) { update_cut(__builtin_ctzll(bit), level, ply); break; }   //[C]
				}
			}
			else
			{
				for(const unsigned long long mask: move_order)
				{
					unsigned long long h = hand & mask;
					hand ^= h;
					while (h)
					{
						const unsigned long long bit = h & -h;
						BoardInc2 b = board.place_fast_clone(bit);
						enum State r = Board::win(b.b.You);

						assert(r == State::Continue);
						int ev;
#if USE_PVS
						if (!pv_done)
						{
							ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);       // 最初の手: フル
						}
						else
						{
							ev = -evaluate_board(b, level - 1, -alpha - 1, -alpha, ply + 1);  // null window
							if (alpha < ev && ev < beta)
								ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);   // fail high → 再探索
						}
#else
						ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);           // 提案4版と同一
#endif
						pv_done = true;
						if (ev > alpha) { alpha = ev; best_move = (unsigned char)__builtin_ctzll(bit); }
						if (alpha >= beta) { update_cut(__builtin_ctzll(bit), level, ply); break; }   //[C]
						h ^= bit;
					}
					if (alpha >= beta) break;
				}
			}
#else
#if USE_LAZYSORT
			// ★[A'] 残りの合法手を u64 キー(score << 6 | sq)で固定長配列に収集。
			//   pair(score, bit) の降順 == (score 降順、同点なら sq 降順) == キーの降順。score は非負・31 bit 以内。
			unsigned long long keys[16];
			int n = 0;
			int group = 2;                                   // 静的 move_order のグループボーナス(核=2, 中=1, 1段目=0)
			for (const unsigned long long mask : move_order)
			{
				unsigned long long h = hand & mask;
				hand ^= h;
				while (h)
				{
					const unsigned long long bit = h & -h;
					const int sq = __builtin_ctzll(bit);
					unsigned long long score = (unsigned)(history[sq] * 4 + group);   // history 主、静的順は同点時のタイブレーク
					if      (sq == killer[ply][0]) score = (unsigned)INT_MAX;          // killer 1st は最優先
					else if (sq == killer[ply][1]) score = (unsigned)INT_MAX - 1;      // killer 2nd はその次
					keys[n++] = score << 6 | (unsigned)sq;
					h ^= bit;
				}
				group--;
			}

			// ★[B'] 探索本体。ソートせず、各反復で「残りの最大キー」を先頭へ持ってくる(選択ソートの 1 段)。
			//   探索順は [A]+std::sort と同一。βカットで抜ければ残りの比較はしない。
			for (int i = 0; i < n; i++)
			{
				int m = i;
				for (int j = i + 1; j < n; j++) if (keys[j] > keys[m]) m = j;
				swap(keys[i], keys[m]);
				const int sq = (int)(keys[i] & 63);
				const unsigned long long bit = 1uLL << sq;
				BoardInc2 b = board.place_fast_clone(bit);
				enum State r = Board::win(b.b.You);

				assert(r == State::Continue);
				int ev;
#if USE_PVS
				if (!pv_done)
				{
					ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);       // 最初の手: フル
				}
				else
				{
					ev = -evaluate_board(b, level - 1, -alpha - 1, -alpha, ply + 1);  // null window
					if (alpha < ev && ev < beta)
						ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);   // fail high → 再探索
				}
#else
				ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
#endif
				pv_done = true;
				if (ev > alpha) { alpha = ev; best_move = (unsigned char)sq; }
				if (alpha >= beta) { update_cut(sq, level, ply); break; }   //[C]
			}
#else
			// [A] 残りの合法手をスコア付きで固定長配列に収集(提案4のまま)
			array<pair<int, unsigned long long>, 16> moves;
			int n = 0;
			int group = 2;                                   // 静的 move_order のグループボーナス(核=2, 中=1, 1段目=0)
			for (const unsigned long long mask : move_order)
			{
				unsigned long long h = hand & mask;
				hand ^= h;
				while (h)
				{
					const unsigned long long bit = h & -h;
					const int sq = __builtin_ctzll(bit);
					int score = history[sq] * 4 + group;     // history 主、静的順は同点時のタイブレーク
					if      (sq == killer[ply][0]) score = INT_MAX;      // killer 1st は最優先
					else if (sq == killer[ply][1]) score = INT_MAX - 1;  // killer 2nd はその次
					moves[n++] = make_pair(score, bit);
					h ^= bit;
				}
				group--;
			}
			sort(moves.begin(), moves.begin() + n, greater<pair<int, unsigned long long>>());

			// [B] 探索本体(★PVS: 最初の手のみフル、以降 null window → fail high 時のみ再探索)
			for (int i = 0; i < n; i++)
			{
				const unsigned long long bit = moves[i].second;
				const int sq = __builtin_ctzll(bit);
				BoardInc2 b = board.place_fast_clone(bit);
				enum State r = Board::win(b.b.You);

				assert(r == State::Continue);
				int ev;
#if USE_PVS
				if (!pv_done)
				{
					ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);       // 最初の手: フル
				}
				else
				{
					ev = -evaluate_board(b, level - 1, -alpha - 1, -alpha, ply + 1);  // null window
					if (alpha < ev && ev < beta)
						ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);   // fail high → 再探索
				}
#else
				ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);           // 提案4版と同一
#endif
				pv_done = true;
				if (ev > alpha) { alpha = ev; best_move = (unsigned char)sq; }
				if (alpha >= beta) { update_cut(sq, level, ply); break; }   //[C]
			}
#endif  // USE_LAZYSORT
#endif
		}

		//[4] store
		const unsigned char bound =
			alpha <= alpha_orig ? TT_UPPER :        // どの手も alpha を上げられず(上界)
			alpha >= beta       ? TT_LOWER :        // βカット(下界)
			                      TT_EXACT;
		tt.store(key, alpha, level, bound, best_move);
		return alpha;
	}

	pair<int, int> move(Board board) override
	{
		tt.new_search();   // 世代更新(表クリアはしない。前の手の結果は上書きされるまで再利用される)
		memset(killer, TT_NO_MOVE, sizeof(killer));   // 手番ごとにリセット(TT_NO_MOVE = 0xFF)
		memset(history, 0, sizeof(history));

		unsigned long long hand = board.valid_move();
		assert(hand);

		{
			const unsigned long long r = hand & Board::reach(board.Me);
			if (r)
			{
				int v = __builtin_ctzll(r);
				return make_pair(X(v), Y(v));
			}
		}
		{
			const unsigned long long r = hand & Board::reach(board.You);
			if (r) hand = r;
		}

		// ランダム手も相手リーチ阻止後の hand から選ぶ(案①)。
		// 相手リーチがあれば hand は阻止手に絞られているため即死を避けられる。
		// 相手リーチが無ければ hand は全合法手のままで従来と同一挙動。
		if (random && AI_RNG() % 100 < random) return move_random_hand(hand);

		unsigned long long mv = 0uLL;
		int mx = -INF;
		const int turn = board.turn();// turn number (the number of stones = turn - 1)

		// ★7c: root で一度だけ Board → BoardInc 変換(以降の探索は BoardInc 系)
		const BoardInc2 bi = BoardInc2::from(board);

#if USE_ID
		// ---- 反復深化(root-only)----------------------------------------------
		// ★最終読み深さは原本 main と同一の turn 依存式にする(evaluate_board へ渡す深さ d)。
		//   総読み手数 N = d + 1。turn>=39 の d=22 は N=23(奇数手読み)になる点に注意(§1.3 caveat)。
		//   終盤は葉が終端局面(勝敗確定)で評価関数を経由しないため実用上は成立するが、
		//   奇数手読みは評価視点前提から外れる。偶数手読みを厳守したい場合は d_target を偶数にすること。
		// const int d_target = turn>=39?23:turn>=31?11:turn>=23?9:level - 1;//教師データ用ver6,シグモイド関数の係数は1840
		const int d_target = YON_DEPTH_TARGET(turn, level);//教師データ用ver7,シグモイド関数の係数は1840(既定展開 = turn>=37?25:turn>=29?11:turn>=21?9:level-1)

		// root 手を固定長配列に収集(強制手絞り込み後の hand。合法手は最大16)。
		// 初期順は静的 move_order のグループ順(現行 dynamic 収集と同じ走査順)。
		array<pair<int, unsigned long long>, 16> roots;   // (score, bit)。score は直近反復の評価値
		int n = 0;
		for (const unsigned long long mask : move_order)
		{
			unsigned long long h = hand & mask;
			while (h)
			{
				const unsigned long long bit = h & -h;
				roots[n++] = make_pair(0, bit);
				h ^= bit;
			}
		}

		// 深さ d を 2 手ずつ深化し、最終反復で必ず d_target に着地させる。
		// 開始 d は d_target とパリティを合わせる(通常は d=3=旧4手読み。d_target が偶数なら d=4 から)。
		// これにより浅い反復の TT ウォームアップを効かせつつ、最終 d を原本と一致させる。
		int d_start = (((d_target - 3) & 1) == 0) ? 3 : 4;
		if (d_start > d_target) d_start = d_target;
		for (int d = d_start; d <= d_target; d += 2)
		{
			mx = -INF;
			mv = 0uLL;
			for (int i = 0; i < n; i++)
			{
				const unsigned long long bit = roots[i].second;
				BoardInc2 b = bi.place_fast_clone(bit);
				enum State r = Board::win(b.b.You);

				assert(r == State::Continue);
				int ev;
#if USE_PVS
				if (mx == -INF)
				{
					ev = -evaluate_board(b, d, -INF, -mx + 1, 0);       // 最初の手: 現行と同じ窓
				}
				else
				{
					ev = -evaluate_board(b, d, -mx - 1, -mx + 1, 0);    // 親窓 (mx-1, mx+1) の null window
					if (ev >= mx + 1)
						ev = -evaluate_board(b, d, -INF, -mx, 0);       // fail high → 親窓 (mx, INF) で確定
				}
#else
				ev = -evaluate_board(b, d, -INF, -mx + 1, 0);           // 提案4版と同一
#endif
				roots[i].first = ev;                                    // 次反復の並べ替えキー
				if (mx < ev) mv = 0uLL, mx = ev;
				if (mx == ev) mv |= bit;
			}
			// 次の(深い)反復を最善手優先にする。stable_sort で同点手の相対順(=静的 move_order)を維持。
			// score 同点時に bit 値で比較しないよう、キーを score のみに限定するラムダ比較を用いる(§3.3-2)。
			stable_sort(roots.begin(), roots.begin() + n,
			            [](const pair<int, unsigned long long>& a, const pair<int, unsigned long long>& b)
			            { return a.first > b.first; });
		}
		// ループ後、最終反復(N == N_target = level)の mx / mv がそのまま採用される。
		// ----------------------------------------------------------------------
#else
		//4手読みパート(root は1手番に1回のみでコスト無視できるため現行のまま。提案4 §1.1)
		array<pair<int, unsigned long long>, 16> dynamic;   // 提案3: vector → スタック固定長(合法手は最大16)
		int n = 0;                                          // 提案3: 要素数
		for (const unsigned long long mask: move_order)
		{
			unsigned long long h = hand & mask;
			hand ^= h;
			while (h)
			{
				const unsigned long long bit = h & -h;
				BoardInc2 b = bi.place_fast_clone(bit);
				enum State r = Board::win(b.b.You);

				assert(r == State::Continue);
				int ev = -evaluate_board(b, 3 , -INF , INF, 0);
				dynamic[n++] = make_pair(ev, bit);          // 提案3: push_back → 添字代入
				h ^= bit;
			}
		}
		sort(dynamic.begin(), dynamic.begin() + n, greater<pair<int, unsigned long long>>());  // 提案3: 降順(rbegin/rend と結果列一致)

		for(int i = 0; i < n; i++)                          // 提案3: dynamic.size() → n
		{
			const unsigned long long bit = dynamic[i].second;
			BoardInc2 b = bi.place_fast_clone(bit);
			enum State r = Board::win(b.b.You);

			assert(r == State::Continue);
			const int depth = turn>=39?22:turn>=31?11:turn>=23?9:level - 1;//教師データ用ver6,シグモイド関数の係数は1840
			// const int depth = level - 1;
			int ev;
#if USE_PVS
			if (mx == -INF)
			{
				ev = -evaluate_board(b, depth, -INF, -mx + 1, 0);       // 最初の手: 現行のまま
			}
			else
			{
				ev = -evaluate_board(b, depth, -mx - 1, -mx + 1, 0);    // 親窓 (mx-1, mx+1) の null window
				if (ev >= mx + 1)
					ev = -evaluate_board(b, depth, -INF, -mx, 0);       // fail high → 親窓 (mx, INF) で確定
				// ev == mx なら同点(窓内で exact)、ev <= mx-1 なら棄却。いずれも再探索不要
			}
#else
			ev = -evaluate_board(b, depth, -INF, -mx + 1, 0);           // 提案4版と同一
#endif
			if (mx < ev) mv = 0uLL, mx = ev;
			if (mx == ev) mv |= bit;
		}
#endif

		enum Color now = board.validate();
		if(turn % 2 == 0)
		{
			game->evaluatessec_tmp[turn / 2] = mx;
		}
		else
		{
			game->evaluatesfir_tmp[(turn + 1) / 2] = mx;
		}
		if (verbose)
		{
			if (now == Color::Black) cout<<"\033[31m";
			cout << "score = " << mx << " by";
			for (int xyz = 0; xyz < BOARD_SIZE; xyz++) if (mv & 1uLL << xyz)
			{
				cout << " (" << X(xyz) + 1 << ", " << Y(xyz) + 1 << ", " << Z(xyz) + 1 << "),";
			}
			cout << endl;
			cout << "win : " << 100 / (1 + exp((double)-mx / 400)) << " %";
			if (now == Color::Black) cout<<"\033[m";
			cout<<endl;
		}
		assert(mv);
		{
			vector<pair<int, int> > XY;
			for (int xyz = 0; xyz < BOARD_SIZE; xyz++) if (mv & 1uLL << xyz) XY.emplace_back(X(xyz), Y(xyz));
			return XY[AI_RNG() % XY.size()];
		}
	}
};
