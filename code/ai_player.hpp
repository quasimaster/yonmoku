#pragma once

#include "game.hpp"

template<typename F>
pair<unsigned long long, int> read_DFS(Board board, int level, const F& evaluate_func)
{
	if (level == 0) return make_pair(0uLL, evaluate_func(board));

	assert(level >= 1);
	unsigned long long hand = board.valid_move();
	if (!hand) return make_pair(0uLL, 0);

	{//reach
		{
			const unsigned long long r = hand & Board::reach(board.Me);
			if (r) return make_pair(r, INF);
		}
		{
			const unsigned long long r = hand & Board::reach(board.You);
			if (r) hand = r;
		}
	}

	pair<unsigned long long, int> mv = make_pair(0uLL, -INF);
	while (hand)
	{
		const unsigned long long bit = hand & -hand;
		Board b = board;
		enum State r = b.place_fast(bit);

		assert(r == State::Continue);
		int ev = -read_DFS(b, level - 1, evaluate_func).second;
		if (ev > INF - BOARD_SIZE * 2) ev = ev - 1;
		else if (ev < -INF + BOARD_SIZE * 2) ev = ev + 1;
		if (mv.second < ev) mv = make_pair(0uLL, ev);
		if (mv.second == ev) mv.first |= bit;
		hand ^= bit;
	}
	assert(mv.first);
	return mv;
}

template<typename F>
struct AIPlayer : Player
{
	using Player::verbose;
	using Player::random;
	int level;
	F evaluate_func;
	Game* game = nullptr;
	AIPlayer(int level, F evaluate_func) : level(level), evaluate_func(evaluate_func) { assert(level >= 1); }

	void set_game(Game* g) { game = g; }

	//int evaluate_board(Board board, int level, int alpha, int beta)
	int evaluate_board(Board board, int level, int alpha, int beta)
	{
		unsigned long long hand = board.valid_move();
		if (!hand) return 0;

		{//reach
			{
				const unsigned long long r = hand & Board::reach(board.Me);
				if (r) return INF - board.turn();
			}
			{
				const unsigned long long r = Board::reach(board.You);
				if (hand & r) hand = hand & r;
				else if (level <= 0) return evaluate_func(board);
				hand &= ~(r >> SIZE * SIZE);
				if (!hand) return -(INF - (board.turn() + 1));
			}
		}

		const int turn = board.turn();// turn number (the number of stones = turn - 1)
        //if(level >= 8 && turn < 27 || level >= 10 && turn >= 27)
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
                    // Board b = board;
                    // enum State r = b.place_fast(bit);

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
                {
                    const unsigned long long bit = dynamic[i].second;
                    // Board b = board;
                    // enum State r = b.place_fast(bit);

					Board b = board.place_fast_clone(bit);
					enum State r = Board::win(b.You);

                    assert(r == State::Continue);
                    int ev = -evaluate_board(b, level - 1, -beta, -alpha);
                    alpha = max(alpha, ev);
                    if (alpha >= beta) break;
                }
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
                    //const unsigned long long bit = dynamic[i].second;
                    // Board b = board;
                    // enum State r = b.place_fast(bit);

					Board b = board.place_fast_clone(bit);
					enum State r = Board::win(b.You);

                    assert(r == State::Continue);
                    int ev = -evaluate_board(b, level - 1, -beta, -alpha);
                    alpha = max(alpha, ev);
                    if (alpha >= beta) break;
                    h ^= bit;
                }
                if (alpha >= beta) break;
            }
        }
		return alpha;
	}

	pair<int, int> move(Board board) override
	{
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
				// Board b = board;
				// enum State r = b.place_fast(bit);

				Board b = board.place_fast_clone(bit);
				enum State r = Board::win(b.You);

				assert(r == State::Continue);
				int ev = -evaluate_board(b, 3 , -INF , INF);
				//if (mx < ev) mv = 0uLL, mx = ev;
				//if (mx == ev) mv |= bit;
                dynamic.push_back(make_pair(ev, bit));
				h ^= bit;
			}
		}
        sort(dynamic.rbegin(), dynamic.rend());

	    //while (hand)//
        for(int i = 0; i < dynamic.size(); i++)
        //for (const unsigned long long mask: move_order)
		{
            //unsigned long long h = hand & mask;
            //unsigned long long h = hand & dynamic[i].second;
			//hand ^= h;
			//while (h)
			{
				//const unsigned long long bit = h & -h;
                const unsigned long long bit = dynamic[i].second;
				// Board b = board;
				// enum State r = b.place_fast(bit);

				Board b = board.place_fast_clone(bit);
				enum State r = Board::win(b.You);

				assert(r == State::Continue);//下の行について、?nはn+1手読みturn>=45?19:turn>=43?15:turn>=41?13:turn>=39?11:turn>=33?9
				//int ev = -evaluate_board(b,turn>=46?14:turn>=39?9:level - 1, -INF , -mx + 1);
				//int ev = -evaluate_board(b,turn>=44?16::level - 1, -INF , -mx + 1);//教師データ用ver3
                //int ev = -evaluate_board(b,turn>=43?17:turn>=35?9:level - 1, -INF , -mx + 1);//教師データ用ver4,シグモイド関数の係数は920
				// int ev = -evaluate_board(b,turn>=40?21:turn>=33?11:turn>=25?9:level - 1, -INF , -mx + 1);//教師データ用ver5,シグモイド関数の係数は1840
				int ev = -evaluate_board(b,turn>=39?22:turn>=31?11:turn>=23?9:level - 1, -INF , -mx + 1);//教師データ用ver6,シグモイド関数の係数は1840
                //int ev = -evaluate_board(b, turn>=39?21:turn>=37?12:turn>=29?10:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				//int ev = -evaluate_board(b, turn>=39?21:turn>35?13:turn>=29?11:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				// int ev = -evaluate_board(b, turn>=39?22:turn>=33?13:turn>=21?11:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				if (mx < ev) mv = 0uLL, mx = ev;
				if (mx == ev) mv |= bit;
				//h ^= bit;
			}
		}

		//const int turn = board.turn();// turn number (the number of stones = turn - 1)
		//auto[mv, ev] = read_DFS(board, turn >= 40 ? level : level, evaluate_func);
		enum Color now = board.validate();
		if(turn % 2 == 0)
		{
			//evaluatessec[game_count][turn >> 1] = mx;
			game->evaluatessec_tmp[turn / 2] = mx;
			//cout << "score game_count = " << game_count << endl;
		}
		else
		{
			//evaluatesfir[game_count][turn + 1 >> 1] = mx;
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

template<typename F>
struct AIPlayer_minimax : Player
{
	using Player::verbose;
	int level;
	F evaluate_func;
	AIPlayer_minimax(int level, F evaluate_func) : level(level), evaluate_func(evaluate_func) { assert(level >= 1); }

	pair<int, int> move(Board board) override
	{
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
			if (r)
			{
				int v = __builtin_ctzll(r);
				return make_pair(X(v), Y(v));
			}
		}

		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		auto[mv, ev] = read_DFS(board, turn >= 40 ? level : level, evaluate_func);
		enum Color now = board.validate();
		if (verbose)
		{
			if (now == Color::Black) cout<<"\033[31m";
			cout << "score = " << ev << " by";
			for (int xyz = 0; xyz < BOARD_SIZE; xyz++) if (mv & 1uLL << xyz)
			{
				cout << " (" << X(xyz) + 1 << ", " << Y(xyz) + 1 << ", " << Z(xyz) + 1 << "),";
			}
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
