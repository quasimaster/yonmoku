#pragma once

#include "common.hpp"
#include "board.hpp"

struct Player
{
	bool verbose;
	int random;
	Player() : verbose(false), random(0) {}
	void set_verbose(bool verbose_) {verbose = verbose_;}
	void set_random(int random_) {random = random_;}
	pair<int, int> move_random(Board board)
	{
		unsigned long long hand = board.valid_move();
		assert(hand);

		const int sz = __builtin_popcountll(hand);
		int idx = rng() % sz + 1;
		int v = 0;
		for (; v < 64; v++) if (hand >> v & 1)
		{
			idx--;
			if (idx == 0) break;
		}
		assert(idx == 0);

		if (verbose) cout << "random move (" << X(v) + 1 << ", " << Y(v) + 1 << ", " << Z(v) + 1 << ")" << endl;
		return make_pair(X(v), Y(v));
	}
	virtual pair<int, int> move(Board board) = 0;
	virtual bool is_human() const { return false; }   // 既定は非人間(AI・自己対戦は override しない)

};

struct HumanPlayer : Player
{
	bool is_human() const override { return true; }

	pair<int, int> move(Board board) override
	{
		enum Color now = board.validate();
		cout << endl;
		board.print();
		cout << "Input x y: place ";
		if (now == Color::Black) cout << "\033[31mX\033[m";
		else cout << "O";
		cout << " to (x, y)\t(1 <= x, y <= 4)  [enter an out-of-range coord to undo]"<<endl;
		int x, y;
		if (!(cin >> x >> y))            // 数値以外 / EOF 等の入力失敗 → undo 扱い
		{
			cin.clear();
			string dummy; cin >> dummy;  // 不正トークンを 1 つ読み捨て
			return UNDO_MOVE;
		}
		if (x < 1 || x > 4 || y < 1 || y > 4) return UNDO_MOVE;   // 範囲外 → undo
		return make_pair(x - 1, y - 1);                            // 通常手
	}
};
