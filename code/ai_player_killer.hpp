#pragma once

#include <climits>
#include <cstring>

#include "game.hpp"
#include "tt.hpp"

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

// 提案4(killer move / history heuristic)版。ai_player_tt_leaf_array.hpp の
// AIPlayerTTLeafArray(提案1+2+3 実装済み)のコピーで、差分は
//   - killer[MAX_PLY][2] / history[64] の追加と move() 先頭でのリセット
//   - evaluate_board への ply 引数の追加(root = 0、再帰で +1)
//   - 4手読みパートの撤去と killer/history ordering への置換(USE_DEEP_ORDER=1 で温存)
//   - βカット箇所での killer / history 更新
// (実装計画書 implementation-plan-killer-history.md §3。基準は main_alpha_tt_leaf_array.cpp)
template<typename F>
struct AIPlayerKiller : Player
{
	using Player::verbose;
	using Player::random;
	int level;
	F evaluate_func;
	Game* game = nullptr;
	TranspositionTable tt;    // インスタンス毎(スレッド間・プレイヤー間で共有しない)
	static const int MAX_PLY = 64;
	unsigned char killer[MAX_PLY][2];   // βカットを起こした手(マス番号)。未設定 = TT_NO_MOVE
	int history[64];                    // history[sq] += level * level(1 << 28 で飽和)
	AIPlayerKiller(int level, F evaluate_func, int tt_bits = 22) : level(level), evaluate_func(evaluate_func), tt(tt_bits) { assert(level >= 1); }

	void set_game(Game* g) { game = g; }

	// [C] βカットを起こした手 sq の killer / history 更新
	inline void update_cut(int sq, int level, int ply)
	{
		if (sq != killer[ply][0]) { killer[ply][1] = killer[ply][0]; killer[ply][0] = (unsigned char)sq; }
		history[sq] = min(history[sq] + level * level, 1 << 28);   // 飽和(手番リセット前の桁あふれ保険)
	}

	int evaluate_board(Board board, int level, int alpha, int beta, int ply)
	{
#ifdef BENCH
		g_node_count++;
#endif
		unsigned long long hand = board.valid_move();
		if (!hand) return 0;

		//[1] probe
		const unsigned long long key = TranspositionTable::hash(board);
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

		{//reach (既存のまま。即勝ち/即負けの return は格納しない)
			const unsigned long long rMe_raw = Board::reach(board.Me);   // 提案2: スコープ外へ持ち上げ
			{
				const unsigned long long r = hand & rMe_raw;
				if (r) return INF - board.turn();
			}
			const unsigned long long rYou_raw = Board::reach(board.You); // 提案2: 名前を付けて保持
			{
				if (hand & rYou_raw) hand = hand & rYou_raw;
				else if (level <= 0)
				{
					const int ev = evaluate_func(board, rMe_raw, rYou_raw, hand);  // 提案2: 再計算排除
#if TT_STORE_LEAF
					tt.store(key, ev, 0, TT_EXACT, TT_NO_MOVE);   //[2] 葉も depth0 で格納
#endif
					return ev;
				}
				hand &= ~(rYou_raw >> SIZE * SIZE);
				if (!hand) return -(INF - (board.turn() + 1));
			}
		}

		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		unsigned char best_move = TT_NO_MOVE;

		//[3] TT best_move を最初に試す(強制手絞り込み後の hand で合法性確認)
		if (tt_move != TT_NO_MOVE && (hand >> tt_move & 1))
		{
			const unsigned long long bit = 1uLL << tt_move;
			Board b = board.place_fast_clone(bit);
			int ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
			if (ev > alpha) { alpha = ev; best_move = tt_move; }
			if (alpha >= beta) update_cut(tt_move, level, ply);   //[C] TT move でのβカットも更新(§3.3)
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
						Board b = board.place_fast_clone(bit);
						enum State r = Board::win(b.You);

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
					Board b = board.place_fast_clone(bit);
					enum State r = Board::win(b.You);

					assert(r == State::Continue);
					int ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
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
						Board b = board.place_fast_clone(bit);
						enum State r = Board::win(b.You);

						assert(r == State::Continue);
						int ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
						if (ev > alpha) { alpha = ev; best_move = (unsigned char)__builtin_ctzll(bit); }
						if (alpha >= beta) { update_cut(__builtin_ctzll(bit), level, ply); break; }   //[C]
						h ^= bit;
					}
					if (alpha >= beta) break;
				}
			}
#else
			// [A] 残りの合法手をスコア付きで固定長配列に収集(提案3の構造を流用)
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

			// [B] 探索本体(現行の静的ループの中身と同一)
			for (int i = 0; i < n; i++)
			{
				const unsigned long long bit = moves[i].second;
				const int sq = __builtin_ctzll(bit);
				Board b = board.place_fast_clone(bit);
				enum State r = Board::win(b.You);

				assert(r == State::Continue);
				int ev = -evaluate_board(b, level - 1, -beta, -alpha, ply + 1);
				if (ev > alpha) { alpha = ev; best_move = (unsigned char)sq; }
				if (alpha >= beta) { update_cut(sq, level, ply); break; }   //[C]
			}
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

		if (random && rng() % 100 < random) return move_random(board);

		unsigned long long mv = 0uLL;
		int mx = -INF;
		const int turn = board.turn();// turn number (the number of stones = turn - 1)

		//4手読みパート(root は1手番に1回のみでコスト無視できるため現行のまま。§1.1)
		array<pair<int, unsigned long long>, 16> dynamic;   // 提案3: vector → スタック固定長(合法手は最大16)
		int n = 0;                                          // 提案3: 要素数
		for (const unsigned long long mask: move_order)
		{
			unsigned long long h = hand & mask;
			hand ^= h;
			while (h)
			{
				const unsigned long long bit = h & -h;
				Board b = board.place_fast_clone(bit);
				enum State r = Board::win(b.You);

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
			Board b = board.place_fast_clone(bit);
			enum State r = Board::win(b.You);

			assert(r == State::Continue);
			int ev = -evaluate_board(b,turn>=39?22:turn>=31?11:turn>=23?9:level - 1, -INF , -mx + 1, 0);//教師データ用ver6,シグモイド関数の係数は1840
			if (mx < ev) mv = 0uLL, mx = ev;
			if (mx == ev) mv |= bit;
		}

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
			return XY[rng() % XY.size()];
		}
	}
};
