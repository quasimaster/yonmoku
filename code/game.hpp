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
			if (xy == UNDO_MOVE) return State::Undo;   // undo 要求。盤面・hand には一切コミットしない
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

	// hand[i] を打った担当プレイヤー(定跡手 i < start.size() には使わない)
	Player* player_at(int i) const { return (i % 2 == 0) ? player1 : player2; }

	// undo: 末尾の「相手(非人間)手」を全て + 続く「人間手」1 つを取り消し、盤面を再生する。
	// 呼び出し時点で不変条件 hand.size() == turn が成立している。戻せなければ turn を据え置く。
	int rewind(int turn)
	{
		const int floor = (int)start.size();   // 定跡手は戻さない下限
		int j = (int)hand.size();              // == turn

		while (j > floor && !player_at(j - 1)->is_human()) j--;   // 末尾の非人間(相手)手を読み飛ばす

		if (!(j > floor && player_at(j - 1)->is_human()))   // 取り消せる自分(人間)の手が無い
		{
			cout << "No move to undo" << endl;
			return turn;             // no-op(局面不変。同じ手番を再度促す)
		}
		const int k = j - 1;   // その人間手 + それ以降の相手手 をまとめて取り消した後の手数

		hand.resize(k);              // 履歴を切り詰め
		board = Board();             // 空盤から
		for (int i = 0; i < k; i++)  // 残りを再生(常に合法手なので余計な表示は出ない)
			board.place(hand[i].first, hand[i].second);
		if (verbose)
		{
			cout << "-- undo: rewound from move " << turn << " to move " << k << " --" << endl;
			board.print();
		}
		return k;                    // 新しい turn(= 打ち直す手番)
	}

	enum Color game()
	{
		enum State ret = State::Continue;
		int turn = 0;
		while (turn < BOARD_SIZE)
		{
			ret = move(turn);
			if (ret == State::Undo) { turn = rewind(turn); continue; }   // 巻き戻してその手番を打ち直す
			if (ret == State::End) break;
			turn++;
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
