// =============================================================================
//  player.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  プレイヤーの基底クラス Player と、端末から手を入力する HumanPlayer。
//  AI(ai_player*.hpp の AIPlayer)も Player を継承し、move() を実装する。
//  move() は盤面を受け取り、石を落とす柱 (x, y)(0 始まり)を返す。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================
#pragma once

#include "common.hpp"
#include "board.hpp"

struct Player
{
	bool verbose;   // true なら思考の内容を表示する
	int random;     // AI が序盤にランダムに指す手数(0 ならランダムに指さない)。使い方は AIPlayer 側が決める
	Player() : verbose(false), random(0) {}
	void set_verbose(bool verbose_) {verbose = verbose_;}
	void set_random(int random_) {random = random_;}
	// 合法手の中からランダムに 1手選ぶ。
	pair<int, int> move_random(Board board)
	{
		return move_random_hand(board.valid_move());
	}
	// 指定した候補手の集合 hand からランダムに 1手選ぶ。
	// 呼び出し側で hand を「相手の決勝点をふさぐ手」だけに絞っておけば、
	// ランダムな手でも、ふさぐべき決勝点をふさがずにすぐ負けることを防げる。
	pair<int, int> move_random_hand(unsigned long long hand)
	{
		assert(hand);

		// hand の中の idx番目(1 始まり)の 1 のビットを探す。
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
		return make_pair(X(v), Y(v));   // 返すのは柱 (x, y)。高さは重力で決まる
	}
	// 盤面 board で指す手(柱 (x, y)、0 始まり)を返す。派生クラスで実装する。
	virtual pair<int, int> move(Board board) = 0;
	virtual bool is_human() const { return false; }   // 既定は人間でない(AI・自己対戦では override しない)

};

// 端末から手を入力する人間のプレイヤー。
// 盤上の範囲外の座標や数値でない入力は「一手戻る」(UNDO_MOVE)として扱う(game.hpp の rewind())。
struct HumanPlayer : Player
{
	bool is_human() const override { return true; }

	pair<int, int> move(Board board) override
	{
		enum Color now = board.validate();
		cout << endl;
		board.print();
		// 手番の記号を表示する(先手の白は赤い X、後手の黒は O)。
		cout << "Input x y: place ";
		if (now == Color::White) cout << "\033[31mX\033[m";
		else cout << "O";
		cout << " to (x, y)\t(1 <= x, y <= 4)  [enter an out-of-range coord to undo]"<<endl;
		int x, y;
		if (!(cin >> x >> y))            // 数値でない入力や EOF などで読めなかった → undo として扱う
		{
			cin.clear();
			string dummy; cin >> dummy;  // 読めなかった語を 1つ捨てる
			return UNDO_MOVE;
		}
		if (x < 1 || x > 4 || y < 1 || y > 4) return UNDO_MOVE;   // 範囲外 → undo
		return make_pair(x - 1, y - 1);                            // 通常の手(入力は 1 始まりなので 0 始まりに直す)
	}
};
