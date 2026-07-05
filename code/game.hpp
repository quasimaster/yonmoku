#pragma once

#include "board.hpp"
#include "player.hpp"

// thread_local int evaluatesfir_tmp[33] = {};
// thread_local int evaluatessec_tmp[33] = {};
// thread_local int record_tmp[64] = {};

struct Game
{
	Board board;
	Player* player1;
	Player* player2;
	vector<pair<int, int> > hand, start;
	bool verbose;

	int evaluatesfir_tmp[33] = {};
	int evaluatessec_tmp[33] = {};
	int record_tmp[64] = {};

	Game(Player* p1, Player* p2, bool verbose=false, vector<pair<int, int> > start = {}) : player1(p1), player2(p2), verbose(verbose), start(start)
	{
		p1 -> set_verbose(verbose);
		p2 -> set_verbose(verbose);

		for(int i = 0; i < 33; i++)evaluatesfir_tmp[i] = INF;
		for(int i = 0; i < 33; i++)evaluatessec_tmp[i] = INF;
		for(int i = 0; i < 64; i++)record_tmp[i] = INF;
	}

	enum State move(int turn)
	{
		enum State ret;
		while (true)
		{
			auto st = chrono::system_clock::now();
			pair<int, int> xy;
			if (turn < start.size()) xy = start[turn];
			else
			{
				Player* current_player = (turn % 2 == 0) ? player1 : player2;
				xy = current_player -> move(board);
			}
			ret = board.place(xy.first, xy.second);
			if (ret == State::Invalid)
			{
				cout << "Invalid move : (" << xy.first + 1 << ", " << xy.second + 1 << ")" << endl;
				continue;
			}
			hand.push_back(xy);
			if (verbose)
			{
				auto msec = chrono::duration_cast<std::chrono::milliseconds>(chrono::system_clock::now() - st);
				cout << "[turn " << turn + 1 << "] Place to (" << xy.first + 1 << ", " << xy.second + 1 << ") ";
				if (turn % 2 == 0) cout << "\033[31m(Black)\033[m";
				else cout << "(White)";
				cout << " by " << msec.count() / 1e3 << " sec" << endl;
				board.print();
			}
			break;
		}
		return ret;
	}

	enum Color game()
	{
		enum State ret;
		for (int turn = 0; turn < BOARD_SIZE; turn++)
		{
			ret = move(turn);
			if (ret == State::End) break;
		}
		board.print();
		enum Color result;
		if (ret == State::End)
		{
			evaluatesfir_tmp[0] = 1;
			evaluatessec_tmp[0] = -1;
			cout << "END : winner is ";
			if (board.validate() == Color::White)
			{
				result = Color::Black;
				cout << "\033[31mBlack\033[m";
			}
			else
			{
				evaluatesfir_tmp[0] = -1;
				evaluatessec_tmp[0] = 1;
				result = Color::White;
				cout << "White";
			}
			cout << " by " << hand.size() << " moves" << endl;
		}
		else
		{
			evaluatesfir_tmp[0] = 0;
			evaluatessec_tmp[0] = 0;
			result = Color::Draw;
			cout << "DRAW" << endl;
		}

		int j = 0;
		for(auto [x,y] : hand)
		{
			record_tmp[j] = 4*(3 - y) + x;
			j++;
		}
		{
			cout << "hands :";
			int j = 0;
			for (auto [x,y] : hand)cout << " {" << x << ", " << y << "},";
			cout << endl;
			cout << "\033[31mfirst (vic or def, evaluates...)\033[m : ";
			cout<<"\033[31m";
			for(int i = 0; i < 33; i++) cout << evaluatesfir_tmp[i] << "," ;
			cout<<"\033[m";
			cout << endl;
			cout << "second (vic or def, evaluates...) : ";
			for (int i = 0 ; i<33 ; i++) cout << evaluatessec_tmp[i] << ",";
			cout << endl;
			cout << "record";
			for(int i = 0; i < 64; i++) cout << record_tmp[i] << ",";
            cout << endl;
		}

		return result;
	}
};
