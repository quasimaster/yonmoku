#pragma once

#include "game.hpp"
#include "tt.hpp"

// 葉(level <= 0 の evaluate_func)を depth0 EXACT として格納するか。
// -DTT_STORE_LEAF=0 で無効化してベンチ比較できる(実装計画書 §4.4)
#ifndef TT_STORE_LEAF
#define TT_STORE_LEAF 1
#endif

// 提案2(葉 reach 再計算排除)版。ai_player_tt.hpp の AIPlayerTT のコピーで、差分は
// 「Board::reach の結果に名前を付けて葉まで届け、evaluate_func に 3 引数追加」のみ
// (実装計画書 implementation-plan-leaf-reach-reuse.md §4)
template<typename F>
struct AIPlayerTTLeaf : Player
{
	using Player::verbose;
	using Player::random;
	int level;
	F evaluate_func;
	Game* game = nullptr;
	TranspositionTable tt;    // インスタンス毎(スレッド間・プレイヤー間で共有しない)
	AIPlayerTTLeaf(int level, F evaluate_func, int tt_bits = 22) : level(level), evaluate_func(evaluate_func), tt(tt_bits) { assert(level >= 1); }

	void set_game(Game* g) { game = g; }

	int evaluate_board(Board board, int level, int alpha, int beta)
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
			int ev = -evaluate_board(b, level - 1, -beta, -alpha);
			if (ev > alpha) { alpha = ev; best_move = tt_move; }
			hand &= ~bit;
		}

		if (alpha < beta)
		{
			if(level >= 8 && turn < 46 || level >= 10 && turn >= 46)//教師データ取得用
			{
				//4手読みパート
				vector<pair<int, unsigned long long>> dynamic;
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
						int ev = -evaluate_board(b, 3 , -INF , INF);
						dynamic.push_back(make_pair(ev, bit));
						h ^= bit;
					}
				}
				sort(dynamic.rbegin(), dynamic.rend());

				for(int i = 0; i < dynamic.size(); i++)
				{
					const unsigned long long bit = dynamic[i].second;
					Board b = board.place_fast_clone(bit);
					enum State r = Board::win(b.You);

					assert(r == State::Continue);
					int ev = -evaluate_board(b, level - 1, -beta, -alpha);
					if (ev > alpha) { alpha = ev; best_move = (unsigned char)__builtin_ctzll(bit); }
					if (alpha >= beta) break;
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
						int ev = -evaluate_board(b, level - 1, -beta, -alpha);
						if (ev > alpha) { alpha = ev; best_move = (unsigned char)__builtin_ctzll(bit); }
						if (alpha >= beta) break;
						h ^= bit;
					}
					if (alpha >= beta) break;
				}
			}
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

		//4手読みパート
		vector<pair<int, unsigned long long>> dynamic;
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
				int ev = -evaluate_board(b, 3 , -INF , INF);
				dynamic.push_back(make_pair(ev, bit));
				h ^= bit;
			}
		}
		sort(dynamic.rbegin(), dynamic.rend());

		for(int i = 0; i < dynamic.size(); i++)
		{
			const unsigned long long bit = dynamic[i].second;
			Board b = board.place_fast_clone(bit);
			enum State r = Board::win(b.You);

			assert(r == State::Continue);
			int ev = -evaluate_board(b,turn>=39?22:turn>=31?11:turn>=23?9:level - 1, -INF , -mx + 1);//教師データ用ver6,シグモイド関数の係数は1840
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
