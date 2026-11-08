// =============================================================================
//  game.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  2人のプレイヤーを交互に指させて 1局を進める Game。
//    - 定跡(start)の手順があれば、まずそれを順に指す
//    - 人間の「一手戻る」(undo)に対応する
//    - 対局後に、勝敗・棋譜・各手の評価値を表示する(教師データの材料になる)
//
//  player1 が先手(白)、player2 が後手(黒)である。
//  turn は 0 始まりの手数で、turn が偶数なら白(先手)、奇数なら黒(後手)の手番。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once

#include "board.hpp"
#include "player.hpp"

// thread_local int evaluatesfir_tmp[33] = {};
// thread_local int evaluatessec_tmp[33] = {};
// thread_local int record_tmp[64] = {};

struct Game
{
	Board board;                           // 現在の盤面
	Player* player1;                       // 先手(白)
	Player* player2;                       // 後手(黒)
	vector<pair<int, int> > hand, start;   // hand: 実際に指した手 (x, y) の列 / start: 最初に指す定跡の手順
	bool verbose;                          // true なら 1手ごとに盤面を表示する

	// 教師データ用の記録。AI(ai_player*.hpp)が探索のたびに評価値を書き込む。
	//   evaluatesfir_tmp[k] : 先手(白)の k手目(k = 1..32)の評価値。[0] は勝敗(勝ち 1 / 負け -1 / 引き分け 0)
	//   evaluatessec_tmp[k] : 後手(黒)の k手目の評価値。[0] は同様に後手から見た勝敗
	//   record_tmp[i]       : i手目(0 始まり)に置いた柱の番号 4(3 - y) + x
	// 値が INF のままの要素は「記録なし」(その手を指していない、または定跡の手)。
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

	// turn手目(0 始まり)を 1手指す。
	//   定跡の範囲内(turn < start.size())なら定跡の手を、そうでなければ手番側のプレイヤーの手を使う。
	//   不正な手(盤外・満杯の柱)なら同じプレイヤーにもう一度指させる。
	//   戻り値: 着手の結果(Continue / End)、または人間が一手戻るを選んだときの Undo。
	enum State move(int turn)
	{
		enum State ret;
		while (true)
		{
			auto st = chrono::system_clock::now();   // 思考時間の計測開始
			pair<int, int> xy;
			if (turn < start.size()) xy = start[turn];
			else
			{
				Player* current_player = (turn % 2 == 0) ? player1 : player2;
				xy = current_player -> move(board);
			}
			if (xy == UNDO_MOVE) return State::Undo;   // undo の要求。盤面にも hand にも何も反映しない
			ret = board.place(xy.first, xy.second);
			if (ret == State::Invalid)
			{
				cout << "Invalid move : (" << xy.first + 1 << ", " << xy.second + 1 << ")" << endl;
				continue;
			}
			hand.push_back(xy);
			if (verbose)
			{
				// 「[turn 手数] Place to (x, y) (色) by 秒」を表示する。座標は 1 始まりに直す。先手(白)は赤で表示する。
				auto msec = chrono::duration_cast<std::chrono::milliseconds>(chrono::system_clock::now() - st);
				cout << "[turn " << turn + 1 << "] Place to (" << xy.first + 1 << ", " << xy.second + 1 << ") ";
				if (turn % 2 == 0) cout << "\033[31m(White)\033[m";
				else cout << "(Black)";
				cout << " by " << msec.count() / 1e3 << " sec" << endl;
				board.print();
			}
			break;
		}
		return ret;
	}

	// hand[i] を指した担当プレイヤー(i が偶数なら先手、奇数なら後手)。
	// 定跡の手(i < start.size())には使わない。
	Player* player_at(int i) const { return (i % 2 == 0) ? player1 : player2; }

	// undo の処理。末尾に続く「相手(人間でない側)の手」をすべてと、その前の「人間の手」1つを取り消し、
	// 残りの手を空の盤面から並べ直す。
	// 呼ばれた時点で hand.size() == turn が成り立っている。取り消せる手がなければ turn をそのまま返す。
	// 戻り値: 新しい turn(= 指し直す手数)。
	int rewind(int turn)
	{
		const int floor = (int)start.size();   // 定跡の手は取り消さない(ここが下限)
		int j = (int)hand.size();              // == turn

		while (j > floor && !player_at(j - 1)->is_human()) j--;   // 末尾の相手(人間でない側)の手を飛ばす

		if (!(j > floor && player_at(j - 1)->is_human()))   // 取り消せる人間の手が無い
		{
			cout << "No move to undo" << endl;
			return turn;             // 何もしない(局面はそのまま。同じ手番でもう一度入力を求める)
		}
		const int k = j - 1;   // 人間の手とそれ以降の相手の手をまとめて取り消した後の手数

		hand.resize(k);              // 棋譜を k手に切り詰める
		board = Board();             // 空の盤面から
		for (int i = 0; i < k; i++)  // 残りの手を並べ直す(どれも合法手なので、余計なメッセージは出ない)
			board.place(hand[i].first, hand[i].second);
		if (verbose)
		{
			cout << "-- undo: rewound from move " << turn << " to move " << k << " --" << endl;
			board.print();
		}
		return k;
	}

	// 1局を最後まで進め、勝者の色を返す(引き分けなら Color::Draw)。
	enum Color game()
	{
		enum State ret = State::Continue;
		int turn = 0;
		while (turn < BOARD_SIZE)   // 64マスが埋まるまで
		{
			ret = move(turn);
			if (ret == State::Undo) { turn = rewind(turn); continue; }   // 巻き戻して、その手番から指し直す
			if (ret == State::End) break;                                // 誰かが 4つ並べた
			turn++;
		}
		board.print();
		enum Color result;
		if (ret == State::End)
		{
			// 勝ったのは最後に置いた側。validate() は「次の手番」の色を返すので、
			// それが黒(後手)なら直前に置いたのは白(先手)で、白の勝ち。
			evaluatesfir_tmp[0] = 1;
			evaluatessec_tmp[0] = -1;
			cout << "END : winner is ";
			if (board.validate() == Color::Black)
			{
				result = Color::White;
				cout << "\033[31mWhite\033[m";
			}
			else
			{
				evaluatesfir_tmp[0] = -1;
				evaluatessec_tmp[0] = 1;
				result = Color::Black;
				cout << "Black";
			}
			cout << " by " << hand.size() << " moves" << endl;
		}
		else
		{
			// 64マスが埋まっても 4つ並ばなかった: 引き分け
			evaluatesfir_tmp[0] = 0;
			evaluatessec_tmp[0] = 0;
			result = Color::Draw;
			cout << "DRAW" << endl;
		}

		// 棋譜を柱の番号 4(3 - y) + x に直して記録する(教師データの形式。y を上下反転している)。
		int j = 0;
		for(auto [x,y] : hand)
		{
			record_tmp[j] = 4*(3 - y) + x;
			j++;
		}
		{
			// 棋譜(0 始まりの座標)、先手と後手の評価値の列、柱の番号の棋譜を表示する。
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
