#include<iostream>
#include<queue>
#include<vector>
#include<array>
#include<algorithm>
#include<cassert>
#include<random>
#include<set>
#include<map>
#include<chrono>
#include<string>
#include<fstream>
#include<sstream>
#include <stdlib.h>
# include <stdio.h>
# include <omp.h>

#include "console_utf8.hpp"

using namespace std;

mt19937 rng(random_device{}());
//mt19937 rng;
enum Cell{None, Me, You};
enum State{Continue, End, Invalid};
enum Color{Draw, Black, White};

const int SIZE = 4;
#define IDX(x, y, z) ((x) + (y) * SIZE + (z) * SIZE * SIZE)
#define BIT(x, y, z) (1uLL << IDX(x, y, z))
#define X(idx) ((idx) % SIZE)
#define Y(idx) ((idx) / SIZE % SIZE)
#define Z(idx) ((idx) / SIZE / SIZE)
const int BOARD_SIZE = SIZE * SIZE * SIZE;
const int INF = 1e9;
const int LINES_NUM = 76;

array<unsigned long long, LINES_NUM> LINES;
static const unsigned long long move_order[] = {
	//BIT(0, 0, 0) | BIT(0, 3, 0) | BIT(3, 0, 0) | BIT(3, 3, 0) |
	//BIT(1, 1, 1) | BIT(1, 2, 1) | BIT(2, 1, 1) | BIT(2, 2, 1) |
	//BIT(1, 1, 2) | BIT(1, 2, 2) | BIT(2, 1, 2) | BIT(2, 2, 2) |
	//BIT(0, 0, 3) | BIT(0, 3, 3) | BIT(3, 0, 3) | BIT(3, 3, 3),// first
	//0x9009000006609009uLL,
	0x9009066006609009uLL,//first 核
	//0x0000ffffffff0000uLL,
	0x6ff6f99ff99f0000uLL,//second 1段目以外
	//0x0000ffffffffffffuLL,//4段目以外
	//0xffff0000ffffffffuLL,//3段目以外
	//0xffffffff0000ffffuLL,//2段目以外
	//0xf99ff99ff99ff99fuLL,//真ん中以外
	//0xf99ff99ff99f0000uLL,
	//0xffffffffffff0660uLL,
	//0x0000000090090000uLL,
	//0x0000900900000000uLL,
	//0xffff000000000000uLL,
	0x0000000000006ff6uLL,// last
};

int game_count = -1;
const int sparse = 50;
struct Board
{
	unsigned long long Me, You;
	Board() : Me(0uLL), You(0uLL) {}

	static inline enum State win(const unsigned long long B)
	{
		{//z dir
			unsigned long long b = B & B >> 2 * SIZE * SIZE;
			//static const unsigned long long mask = 0x000000000000ffffuLL;
			if (b & b >> SIZE * SIZE) return State::End;
		}
		{//x dir
			unsigned long long b = B & B >> 2;
			static const unsigned long long mask = 0x1111111111111111uLL;
			if (b & b >> 1 & mask) return State::End;
		}
		{//y dir
			unsigned long long b = B & B >> 2 * SIZE;
			static const unsigned long long mask = 0x000f000f000f000fuLL;
			if (b & b >> SIZE & mask) return State::End;
		}
		{//yz dir
			{
				unsigned long long b = B & B >> 2 * (SIZE * SIZE + SIZE);
				//static const unsigned long long mask = 0x000000000000000fuLL;
				if (b & b >> SIZE * SIZE + SIZE) return State::End;
			}
			{
				unsigned long long b = B & B >> 2 * (SIZE * SIZE - SIZE);
				static const unsigned long long mask = 0x000000000000f000uLL;
				if (b & b >> SIZE * SIZE - SIZE & mask) return State::End;
			}
		}
		{//zx dir
			{
				unsigned long long b = B & B >> 2 * (SIZE * SIZE + 1);
				static const unsigned long long mask = 0x0000000000001111uLL;
				if (b & b >> SIZE * SIZE + 1 & mask) return State::End;
			}
			{
				unsigned long long b = B & B >> 2 * (SIZE * SIZE - 1);
				static const unsigned long long mask = 0x0000000000008888uLL;
				if (b & b >> SIZE * SIZE - 1 & mask) return State::End;
			}
		}
		{//xy dir
			{
				unsigned long long b = B & B >> 2 * (SIZE + 1);
				static const unsigned long long mask = 0x0001000100010001uLL;
				if (b & b >> SIZE + 1 & mask) return State::End;
			}
			{
				unsigned long long b = B & B >> 2 * (SIZE - 1);
				static const unsigned long long mask = 0x0008000800080008uLL;
				if (b & b >> SIZE - 1 & mask) return State::End;
			}
		}
		{//xyz dir
			{
				static const unsigned long long line = BIT(0, 0, 0) | BIT(1, 1, 1) | BIT(2, 2, 2) | BIT(3, 3, 3);
				if ((B & line) == line) return State::End;
			}
			{
				static const unsigned long long line = BIT(0, 0, 3) | BIT(1, 1, 2) | BIT(2, 2, 1) | BIT(3, 3, 0);
				if ((B & line) == line) return State::End;
			}
			{
				static const unsigned long long line = BIT(0, 3, 0) | BIT(1, 2, 1) | BIT(2, 1, 2) | BIT(3, 0, 3);
				if ((B & line) == line) return State::End;
			}
			{
				static const unsigned long long line = BIT(0, 3, 3) | BIT(1, 2, 2) | BIT(2, 1, 1) | BIT(3, 0, 0);
				if ((B & line) == line) return State::End;
			}
		}
		return State::Continue;
	}

	static inline unsigned long long reach(const unsigned long long B)
	{
		unsigned long long ret = 0uLL;
		{//z dir
			const unsigned long long b = B & B >> SIZE * SIZE;
			ret |= B << SIZE * SIZE & b << 3 * SIZE * SIZE;
			ret |= B >> SIZE * SIZE & b << 2 * SIZE * SIZE;
			ret |= b >> SIZE * SIZE & B << SIZE * SIZE;
			ret |= b >> 2 * SIZE * SIZE & B >> SIZE * SIZE;
		}
		{//x dir
			const unsigned long long b = B & B >> 1;
			{
				static const unsigned long long mask = 0x1111111111111111uLL;
				ret |= mask & B >> 1 & b >> 2;
			}
			{
				static const unsigned long long mask = 0x2222222222222222uLL;
				ret |= mask & B << 1 & b >> 1;
			}
			{
				static const unsigned long long mask = 0x4444444444444444uLL;
				ret |= mask & b << 2 & B >> 1;
			}
			{
				static const unsigned long long mask = 0x8888888888888888uLL;
				ret |= mask & b << 3 & B << 1;
			}
		}
		{//y dir
			const unsigned long long b = B & B >> SIZE;
			{
				static const unsigned long long mask = 0x000f000f000f000fuLL;
				ret |= mask & B >> SIZE & b >> 2 * SIZE;
			}
			{
				static const unsigned long long mask = 0x00f000f000f000f0uLL;
				ret |= mask & B << SIZE & b >> SIZE;
			}
			{
				static const unsigned long long mask = 0x0f000f000f000f00uLL;
				ret |= mask & b << 2 * SIZE & B >> SIZE;
			}
			{
				static const unsigned long long mask = 0xf000f000f000f000uLL;
				ret |= mask & b << 3 * SIZE & B << SIZE;
			}
		}
		for (int i = SIZE * SIZE * 3; i < LINES_NUM; i++)
		{
			const unsigned long long b = LINES[i] & ~B;
			if ((b & -b) == b) ret |= b;
		}
		return ret;
	}

	inline enum Cell get_cell(int x, int y, int z) const
	{
		unsigned long long bit = BIT(x, y, z);
		if (Me & bit)return Cell::Me;
		else if (You & bit) return Cell::You;
		else return Cell::None;
	}

	int turn() const
	{
		return __builtin_popcountll(Me | You) + 1;
	}

	enum Color validate() const
	{
		assert(!(Me & You));
		const int d = __builtin_popcountll(Me) - __builtin_popcountll(You);
		assert(d == 0 || d == -1);
		return d == 0 ? Color::Black : Color::White;
	}

	enum Color player() const
	{
		return __builtin_parityll(Me | You) ? Color::White : Color::Black;
	}

	void print() const
	{
		enum Color now = validate();
		unsigned long long black, white;
		if (now == Color::Black) black = Me, white = You;
		else black = You, white = Me;
		if(game_count % sparse == 0)
		cout << "    z=1  z=2  z=3  z=4\n";
		for (int y = SIZE - 1; y >= 0; y--)
		{
			if(game_count % sparse == 0)
			cout << "y=" << y + 1 << " ";
			for (int z = 0; z < SIZE; z++)
			{
				for (int x = 0; x < SIZE; x++)
				{
					const unsigned long long bit = BIT(x, y, z);
					if(game_count % sparse == 0)
					{
						if (black & bit) cout << "\033[31mX\033[m";
						else if (white & bit) cout << "O";
						else cout << "-";
					}
				}
				if(game_count % sparse == 0)
				if (z + 1 < SIZE) cout << " ";
			}
			if(game_count % sparse == 0)
			cout << "\n";
		}
		if(game_count % sparse == 0)
		cout << "  x=1234 1234 1234 1234" << endl;
	}

	array<int, LINES_NUM> count() const
	{
		array<int, LINES_NUM> ret;
		for (int i = 0; i < LINES_NUM; i++)
		{
			if ((Me & LINES[i]) && (You & LINES[i])) ret[i] = 0;
			else if (Me & LINES[i]) ret[i] = __builtin_popcountll(Me & LINES[i]);
			else ret[i] = - __builtin_popcountll(You & LINES[i]);
		}
		return ret;
	}

	enum State place(int x, int y)
	{
		if (x < 0 || 4 <= x || y < 0 || 4 <= y)
		{
			cout << "out of range : (" << x + 1 << ", " << y + 1 << ")" << endl;
			return State::Invalid;
		}
		int z = 0;
		while (z < 4 && get_cell(x, y, z) != Cell::None) z++;
		if (z == 4)
		{
			cout << "row (" << x + 1 << ", " << y + 1 << ") is full" << endl;
			return State::Invalid;
		}
		Me |= BIT(x, y, z);
		swap(Me, You);
		return win(You);
	}

	enum State place_fast(unsigned long long bit)
	{
		Me |= bit;
		swap(Me, You);
		return win(You);
	}

	unsigned long long valid_move() const
	{
		return ((Me | You) << SIZE * SIZE | ((1uLL << SIZE * SIZE) - 1)) & ~(Me | You);
	}
};

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

};

struct HumanPlayer : Player
{
	pair<int, int> move(Board board) override
	{
		enum Color now = board.validate();
		cout << endl;
		board.print();
		cout << "Input x y: place ";
		if (now == Color::Black) cout << "\033[31mX\033[m";
		else cout << "O";
		cout << " to (x, y)\t(1 <= x, y <= 4)"<<endl;
		int x, y;
		cin >> x >> y;
		return make_pair(x - 1, y - 1);
	}
};



int evaluatesfir[100000][34] = {};
int evaluatessec[100000][34] = {};
int record[100001][65] = {};	
//int game_count = -1;
struct Game
{
	Board board;
	Player* player1;
	Player* player2;
	vector<pair<int, int> > hand, start;
	bool verbose;

	//int game_count = 0;

	Game(Player* p1, Player* p2, bool verbose=false, vector<pair<int, int> > start = {}) : player1(p1), player2(p2), verbose(verbose), start(start)
	{
		p1 -> set_verbose(verbose);
		p2 -> set_verbose(verbose);
		game_count = game_count + 1;
		//cout << "in the game game_count = " << game_count << endl;
		for(int i = 0; i < 33; i++)evaluatesfir[game_count][i] = INF;
		for(int i = 0; i < 33; i++)evaluatessec[game_count][i] = INF;
		//cout << "reset game_count = " << game_count << endl;
		
		
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
			//cout << game_count << endl;
			evaluatesfir[game_count][0] = 1;
			evaluatessec[game_count][0] = -1;
			if(game_count % sparse == 0)
			cout << "END : winner is ";
			if (board.validate() == Color::White)
			{
				result = Color::Black;
				if(game_count % sparse == 0)
				cout << "\033[31mBlack\033[m";
			}
			else
			{
				evaluatesfir[game_count][0] = -1;
				evaluatessec[game_count][0] = 1;
				result = Color::White;
				if(game_count % sparse == 0)
				cout << "White";
			}
			if(game_count % sparse == 0)
			cout << " by " << hand.size() << " moves" << endl;
		}
		else
		{
			evaluatesfir[game_count][0] = 0;
			evaluatessec[game_count][0] = 0;
			result = Color::Draw;
			if(game_count % sparse == 0)
			cout << "DRAW" << endl;
		}

		if(game_count % sparse == 0)
		{
			cout << "hands :";
			for (auto [x,y] : hand) cout << " {" << x << ", " << y << "},";
			cout << endl;
			cout << "\033[31mfirst (vic or def, evaluates...)\033[m : ";
			cout<<"\033[31m";
			for (int i = 0 ; i<33 ; i++) cout << evaluatesfir[game_count][i] << ",";
			cout<<"\033[m";
			cout << endl;
			cout << "second (vic or def, evaluates...) : ";
			for (int i = 0 ; i<33 ; i++) cout << evaluatessec[game_count][i] << ",";
			cout << endl;
		}
		
		return result;
	}
};

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
	AIPlayer(int level, F evaluate_func) : level(level), evaluate_func(evaluate_func) { assert(level >= 1); }

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

		for(const unsigned long long mask: move_order)
		{
			unsigned long long h = hand & mask;
			hand ^= h;
			while (h)
			{
				const unsigned long long bit = h & -h;
				Board b = board;
				enum State r = b.place_fast(bit);
				assert(r == State::Continue);
				int ev = -evaluate_board(b, level - 1, -beta, -alpha);
				alpha = max(alpha, ev);
				if (alpha >= beta) break;
				h ^= bit;
			}
			if (alpha >= beta) break;
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

	    //while (hand)//
        for (const unsigned long long mask: move_order)
		{
            unsigned long long h = hand & mask;
			hand ^= h;
			while (h)
			{
				const unsigned long long bit = h & -h;
				Board b = board;
				enum State r = b.place_fast(bit);
				assert(r == State::Continue);//下の行について、?nはn+1手読みturn>=45?19:turn>=43?15:turn>=41?13:turn>=39?11:turn>=33?9
				int ev = -evaluate_board(b,turn>=46?14:level - 1, -INF , -mx + 1);
                //int ev = -evaluate_board(b, turn>=39?21:turn>=37?12:turn>=29?10:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				//int ev = -evaluate_board(b, turn>=39?21:turn>35?13:turn>=29?11:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				if (mx < ev) mv = 0uLL, mx = ev;
				if (mx == ev) mv |= bit;
				h ^= bit;
			}
		}

		//const int turn = board.turn();// turn number (the number of stones = turn - 1)
		//auto[mv, ev] = read_DFS(board, turn >= 40 ? level : level, evaluate_func);
		enum Color now = board.validate();
		if(turn % 2 == 0)
		{
			evaluatessec[game_count][turn >> 1] = mx;
			//cout << "score game_count = " << game_count << endl;
		}
		else
		{
			evaluatesfir[game_count][turn + 1 >> 1] = mx;
		}
		if (verbose)
		{
			if (now == Color::Black) cout<<"\033[31m";
			cout << "score = " << mx << " by";
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

const int pnum = 29;
int A[100001][64][pnum+1];
int pa;
int pb;
int pc;
int pd;
int pe;
int pf;
int pg, ph, pi, pj, pk, pl, pm, pn, po, pp, pq, pr, pt;
int ppa, ppb, ppc, ppd, ppe, ppf, ppg;
int pqa, pqb, pqc, pqd, pqe, pqf, pqg;
unsigned long int parameter_cnt[pnum] = {};//特徴量が何回現れたかを記録

// yonmoku_gradient_descent_second_alpha.cpp では
//   for(int i = 4; i < 18; i = i + 2)//5~18
//   for(int i = 18; i < 32; i = i + 2)//19~32
//   for(int i = 32; i < 46; i = i + 2)//33~46
//   for(int i = 46; i < 60; i = i + 2)//47~60
// のコメントアウトを 1 つずつ切り替えて 4 回実行していた。
// このファイルはその 4 範囲を 1 回の実行で順番に回し、結果をまとめて出力する。
// 勾配降下法の処理そのものは yonmoku_gradient_descent_second_alpha.cpp と同一。
// 教師データの読み込み・特徴量行列 A の構築・parameter_cnt の集計は範囲に依存しないので
// 1 回だけ行う。
struct RangeSpec
{
	const char *label;
	int begin;  // for(int i = begin; i < end; i = i + 2) の begin
	int end;    // 同上 end
};
static const int rangeNum = 4;
static const RangeSpec ranges[rangeNum] =
{
	{"5~18",   4, 18},
	{"19~32", 18, 32},
	{"33~46", 32, 46},
	{"47~60", 46, 60},
};

int main()
{
	//コンソールの出力コードページを UTF-8 に合わせる(日本語の文字化け対策)
	enable_utf8_console();

	{
		vector<unsigned long long> lines;
		for (int x = 0; x < SIZE; x++) for (int y = 0; y < SIZE; y++)
		{
			unsigned long long line = 0uLL;
			for (int z = 0; z < SIZE; z++) line |= BIT(x, y, z);
			lines.push_back(line);
		}
		for (int y = 0; y < SIZE; y++) for (int z = 0; z < SIZE; z++)
		{
			unsigned long long line = 0uLL;
			for (int x = 0; x < SIZE; x++) line |= BIT(x, y, z);
			lines.push_back(line);
		}
		for (int z = 0; z < SIZE; z++) for (int x = 0; x < SIZE; x++)
		{
			unsigned long long line = 0uLL;
			for (int y = 0; y < SIZE; y++) line |= BIT(x, y, z);
			lines.push_back(line);
		}
		for (int x = 0; x < SIZE; x++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int yz = 0; yz < SIZE; yz++)
			{
				line1 |= BIT(x, yz, yz);
				line2 |= BIT(x, yz, SIZE - 1 - yz);
			}
			lines.push_back(line1);
			lines.push_back(line2);
		}
		for (int y = 0; y < SIZE; y++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int zx = 0; zx < SIZE; zx++)
			{
				line1 |= BIT(zx, y, zx);
				line2 |= BIT(zx, y, SIZE - 1 - zx);
			}
			lines.push_back(line1);
			lines.push_back(line2);
		}
		for (int z = 0; z < SIZE; z++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int xy = 0; xy < SIZE; xy++)
			{
				line1 |= BIT(xy, xy, z);
				line2 |= BIT(xy, SIZE - 1 - xy, z);
			}
			lines.push_back(line1);
			lines.push_back(line2);
		}
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL, line3 = 0uLL, line4 = 0uLL;
			for (int xyz = 0; xyz < SIZE; xyz++)
			{
				line1 |= BIT(xyz, xyz, xyz);
				line2 |= BIT(xyz, xyz, SIZE - 1 - xyz);
				line3 |= BIT(xyz, SIZE - 1 - xyz, xyz);
				line4 |= BIT(xyz, SIZE - 1 - xyz, SIZE - 1 - xyz);
			}
			lines.push_back(line1);
			lines.push_back(line2);
			lines.push_back(line3);
			lines.push_back(line4);
		}
		assert(lines.size() == LINES_NUM);
		for (int j = 0; j < LINES_NUM; j++)
		{
			LINES[j] = lines[j];
			assert(__builtin_popcountll(LINES[j]) == 4);
			assert(Board::win(LINES[j]) == State::End);
		}

		unsigned long long ret = 0uLL;
		auto dfs = [&](auto self, int id, unsigned long long B, int rest) -> void
		{
			if (id == 64)
			{
				if (Board::win(B) == State::Continue)
				{
					//ret |= Board::reach_naive(B);
					//ret |= Board::reach(B);
					//assert(Board::reach_naive(B) == Board::reach(B));
				}
			}
			else
			{
				self(self, id + 1, B, rest);
				if (rest > 0) self(self, id + 1, B | 1uLL << id, rest - 1);
			}
		};
		//validation
		//dfs(dfs, 0, 0uLL, 6);
	}
	{//validate move_order
		unsigned long long mv = 0uLL;
		for(unsigned long long mask: move_order) mv |= mask;
		assert(mv == 0xffffffffffffffffuLL);
	}

	auto evaluate = [&](const Board &board) -> int
	{
		int sum = 0;
		for (int v : board.count()) sum += v;
		return sum;
	};
    auto evaluate_pointfir = [&](const Board &board) -> int
	{
		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		int sum = 0;
        if(turn <= 59)
        {
		    //static const int weight[9] = {0,-60,-56,-16,0,16,56,60,0};//first
			const int weight[9] = {0,pa,pb,pc,0,pd,pe,pf,0};//first
		    auto count = board.count();
            for (int v : count) sum += weight[v + 4];

            for(int i = 0; i < LINES_NUM; i++)
            {
                if(count[i] == 2)
                {
                    unsigned long long mr = ~board.Me & LINES[i];
                    static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
                    mr = mr & mask_3;
                    sum += __builtin_popcountll(mr & (~(board.Me | board.You) << SIZE*SIZE)) * pp;
                }
                else if(count[i] == -2)
                {
                    unsigned long long mr = ~board.You & LINES[i];
                    static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
                    mr = mr & mask_3;
                    sum -= __builtin_popcountll(mr & (~(board.Me | board.You) << SIZE*SIZE)) * pq;
                }
            }
        }
        return sum;

	};
    auto evaluate_pointsec = [&](const Board &board, unsigned long long rMe, unsigned long long rYou) -> int
	{
		const unsigned long long rMe_tmp = rMe;
		const unsigned long long rMe_esc = rMe & ~(rYou << SIZE * SIZE);//下に相手のリーチがある場合を削除
		const unsigned long long rYou_esc = rYou & ~(rMe_tmp << SIZE * SIZE);//下に相手のリーチがある場合を削除
		rMe = rMe_esc;
		rYou = rYou_esc;
        
        const int turn = board.turn();// turn number (the number of stones = turn - 1)
		int sum = 0;
        if(turn <= 59)
        {
		    //static const int weight[9] = {0,-60,-56,-16,0,16,56,60,0};//first
			const int weight[9] = {0,0,pb,pc,0,pd,pe,0,0};//first
		    auto count = board.count();
            for (int v : count) sum += weight[v + 4];

            unsigned long long tMe = 0uLL;
            unsigned long long tYou = 0uLL;
            for(int i = 0; i < LINES_NUM; i++)
            {
                if(count[i] == 2)
                {
                    unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
                    static const unsigned long long mask_1 = 0x000000000000ffffuLL;
					static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
                    static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
					static const unsigned long long mask_4 = 0xffff000000000000uLL;
                    unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
					while(floatthree)
					{
						unsigned long long h = floatthree & -floatthree;
						unsigned long long make = two & ~h;//makeT点
                        tMe |= make;
						// unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
						// unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
                    	sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * ppa;//one
						sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * ppb;//two
						sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * ppc;//three
						sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * ppd;//four

						// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * ppe;//two
						// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * ppf;//three
						// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * ppg;//four
						floatthree ^= h;
					}
					
                }
                else if(count[i] == -2)
                {
                    unsigned long long two = ~board.You & LINES[i];
					static const unsigned long long mask_1 = 0x000000000000ffffuLL;
					static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
                    static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
					static const unsigned long long mask_4 = 0xffff000000000000uLL;
					
                    unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
					while(floatthree)
					{
						unsigned long long h = floatthree & -floatthree;
						unsigned long long make = two & ~h;
                        tYou |= make;
						// unsigned long long nonfloat_make = make & ~((board.Me | board.You) << SIZE * SIZE);//浮いてないmakeT点
						// unsigned long long float_make = make & ~nonfloat_make;//浮いているmakeT点
						sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * pqa;
						sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * pqb;
						sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * pqc;
						sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * pqd;

						// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * pqe;//two
						// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * pqf;//three
						// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * pqg;//four
						floatthree ^= h;
					}
                    
                }
            }
            sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * ppe;//T_T
            sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * ppf;//T_W
            sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * ppg;//W_T
            
            sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * pqe;
            sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * pqf;
            sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * pqg;
        }
        return sum;

	};
	auto evaluate_random = [&](const Board &board) -> int
	{
		//int sum = 0;
		//static const int weight[9] = {0,0,0,0,0,0,0,0,0};
		//for (int v : board.count()) sum += weight[v + 4];
		return 0;
	};
	auto continuous = [&](unsigned long long rMe, const unsigned long long rYou) -> int
	{
		rMe &= ~(rYou << SIZE * SIZE);
		return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * po;
	};
	auto reach_layer_intersection = [&](const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand) -> int
	{
		
		const int turn = board.turn();// turn number (the number of stones = turn - 1)

		const unsigned long long rMe_tmp = rMe;
		const unsigned long long rMe_esc = rMe & ~(rYou << SIZE * SIZE);//下に相手のリーチがある場合を削除
		const unsigned long long rYou_esc = rYou & ~(rMe_tmp << SIZE * SIZE);//下に相手のリーチがある場合を削除
		rMe = rMe_esc;
		rYou = rYou_esc;
		
		static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
		static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
		static const unsigned long long mask_4 = 0xffff000000000000uLL;

		const unsigned long long intersection_3 = (rMe & rYou) & mask_3;
		rMe ^= intersection_3;
		rYou ^= intersection_3;

		int sum = 0;
        if(turn <= 59)
        {
			if (now == Color::Black)
            {//first (black) player
                {//Me, first (black) player
                    sum += __builtin_popcountll(rMe & mask_2) * pg;//2nd layer_intersection_fir
                    sum += __builtin_popcountll(rMe & mask_3) * ph;//3rd layer_intersection_fir
                    sum += __builtin_popcountll(rMe & mask_4) * pi;//4th layer_intersection_fir
                }
                {//You, second (white) player
                    sum -= __builtin_popcountll(rYou & mask_2) * pj;//2nd layer_intersection_fir
                    sum -= __builtin_popcountll(rYou & mask_3) * pk;//3rd layer_intersection_fir
                    sum -= __builtin_popcountll(rYou & mask_4) * pl;//4th layer_intersection_fir
                }
                if (intersection_3)
                {//if there exists intersections of reaches on 3rd layer
                    int intersection = __builtin_popcountll(intersection_3);
                    assert(intersection < 5);
                    //if (__builtin_parityll(intersection_3))
                    if(intersection == 1)
                    {//odd, black = Me
                        sum += pm;
                    }
                    else if(intersection == 2)
                    {//even, white = You
                        sum -= pn;
                    }
                    else if(intersection == 3)
                    sum += pr;
					else if(intersection == 4)
					sum -= pt;
                    
                }
            }
            else
            {//second (white) player
                {//Me, second (white) player
                    sum += __builtin_popcountll(rMe & mask_2) * pg;//2nd layer_intersection_sec
                    sum += __builtin_popcountll(rMe & mask_3) * ph;//3rd layer_intersection_sec
                    sum += __builtin_popcountll(rMe & mask_4) * pi;//4th layer_intersection_sec
                }
                {//You, first (black) player
                    sum -= __builtin_popcountll(rYou & mask_2) * pj;//2nd layer_intersection_sec
                    sum -= __builtin_popcountll(rYou & mask_3) * pk;//3rd layer_intersection_sec
                    sum -= __builtin_popcountll(rYou & mask_4) * pl;//4th layer_intersection_sec
                }
                if (intersection_3)
                {//if there exists intersections of reaches on 3rd layer
                    int intersection = __builtin_popcountll(intersection_3);
                    assert(intersection < 5);
                    //if (__builtin_parityll(intersection_3))
                    if(intersection == 1)
                    {//odd, black = Me
                        sum -= pm;
                    }
                    else if(intersection == 2)
                    {//even, white = You
                        sum += pn;
                    }
                    else if(intersection == 3)
                    sum -= pr;
					else if(intersection == 4)
					sum += pt;
                    
                }
            }
        }
		else if(turn >= 60)
		{
			if(now == Color::Black)
			{
				if(rMe & mask_3 || intersection_3) sum = INF - 100000;
				else if(rYou & mask_2 || rYou & mask_4) sum = - INF + 100000;
			}
			else
			{
				if(rMe & mask_4) sum = INF -100000;
				else if(rYou & mask_3 || intersection_3) sum = - INF + 100000;
			}
		}
		return sum;
	};
	auto reach_layer = [&](const Board &board, const enum Color now, unsigned long long rMe, unsigned long long rYou, const unsigned long long hand) -> int
	{
		const unsigned long long rMe_tmp = rMe & ~(hand | rYou << SIZE * SIZE);
		const unsigned long long rYou_tmp = rYou & ~(hand | rMe << SIZE * SIZE);
		rMe = rMe_tmp, rYou = rYou_tmp;
		//rMe &= ~hand;
		//rYou &= ~hand;
		static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
		static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
		static const unsigned long long mask_4 = 0xffff000000000000uLL;

		const int turn = board.turn();// turn number (the number of stones = turn - 1)

		int sum = 0;
		if(turn <= 59)
		{
			if (now == Color::Black)
			{//first (black) player
				{//Me, first (black) player
					sum += __builtin_popcountll(rMe & mask_2) * 48;//2nd layer_fir
					sum += __builtin_popcountll(rMe & mask_3) * 140;//3rd layer_fir
					sum += __builtin_popcountll(rMe & mask_4) * 11;//4th layer_fir
				}
				{//You, second (white) player
					sum -= __builtin_popcountll(rYou & mask_2) * 64;//2nd layer_fir
					sum -= __builtin_popcountll(rYou & mask_3) * 140;//3rd layer_fir
					sum -= __builtin_popcountll(rYou & mask_4) * 16;//4th layer_fir
				}
			}
			else
			{//second (white) player
				{//Me, second (white) player
					sum += __builtin_popcountll(rMe & mask_2) * 48;//2nd layer_sec
					sum += __builtin_popcountll(rMe & mask_3) * 64;//3rd layer_sec
					sum += __builtin_popcountll(rMe & mask_4) * 16;//4th layer_sec
				}
				{//You, first (black) player
					sum -= __builtin_popcountll(rYou & mask_2) * 64;//2nd layer_sec
					sum -= __builtin_popcountll(rYou & mask_3) * 48;//3rd layer_sec
					sum -= __builtin_popcountll(rYou & mask_4) * 16;//4th layer_sec
				}
			}
		}
		else if(turn >= 60)
		{
			if(now == Color::Black)
			{
				if(rMe & mask_3) sum = INF - 100000;
				else if(rYou & mask_2 | rYou & mask_4) sum = - INF + 100000;
			}
			else
			{
				if(rMe & mask_4) sum = INF -100000;
				else if(rYou & mask_3) sum = - INF + 100000;
			}
		}
		return sum;
	};
	auto evaluate_cont = [&](const Board &board) -> int
	{
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		return evaluate(board) + continuous(rMe, rYou) - continuous(rYou, rMe);
	};
	auto evaluate_layer = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate(board) + reach_layer(board,now, rMe, rYou, hand);
	};
	auto evaluate_pointfir_cont_layer = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointfir(board) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer(board,now, rMe, rYou, hand);
	};
	auto evaluate_pointfir_cont_layer_intersection = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointfir(board) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
	};
    auto evaluate_pointsec_cont_layer = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointsec(board, rMe, rYou) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer(board,now, rMe, rYou, hand);
	};
	 auto evaluate_pointsec_cont_layer_intersection = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointsec(board, rMe, rYou) + continuous(rMe, rYou) - continuous(rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
	};
	auto evaluate_pointfir_layer_intersection = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointfir(board) + reach_layer_intersection(board,now, rMe, rYou, hand);
	};

	
	/*
    std::string input_first_evaluate = "/yonmoku/first_evaluate.csv";
	std::string input_second_evaluate = "/yonmoku/second_evaluate.csv";
	std::string input_record = "/yonmoku/record.csv";

	std::ifstream ifs_first_evaluate (input_first_evaluate);
	std::ifstream ifs_second_evaluate (input_second_evaluate);
	std::ifstream ifs_record (input_record);

	std::string str_buf;
	
	int t = 1;
	while(getline(ifs_first_evaluate, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatesfir[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_second_evaluate, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatessec[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_record, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			record[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}

	std::string input_first_evaluate_ver1 = "/yonmoku/first_evaluate_ver2.csv";
	std::string input_second_evaluate_ver1 = "/yonmoku/second_evaluate_ver2.csv";
	std::string input_record_ver1 = "/yonmoku/record_ver2.csv";

	std::ifstream ifs_first_evaluate_ver1 (input_first_evaluate_ver1);
	std::ifstream ifs_second_evaluate_ver1 (input_second_evaluate_ver1);
	std::ifstream ifs_record_ver1 (input_record_ver1);
	
	t = 10001;
	while(getline(ifs_first_evaluate_ver1, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatesfir[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 10001;
	while(getline(ifs_second_evaluate_ver1, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatessec[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 10001;
	while(getline(ifs_record_ver1, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			record[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}*/

	std::string input_first_evaluate_ver3 = "/yonmoku/teacher/first_evaluate_ver7_2_new.csv";
	std::string input_second_evaluate_ver3 = "/yonmoku/teacher/second_evaluate_ver7_2_new.csv";
	std::string input_record_ver3 = "/yonmoku/teacher/record_ver7_2_new.csv";

	std::ifstream ifs_first_evaluate_ver3 (input_first_evaluate_ver3);
	std::ifstream ifs_second_evaluate_ver3 (input_second_evaluate_ver3);
	std::ifstream ifs_record_ver3 (input_record_ver3);

	std::string str_buf;
	
	//t = 34371;
	int t = 1;
	while(getline(ifs_first_evaluate_ver3, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatesfir[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_second_evaluate_ver3, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			evaluatessec[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}
	t = 1;
	while(getline(ifs_record_ver3, str_buf))
	{
		std::istringstream i_stream(str_buf);
		int ev;
		int i = 0;
		while(i_stream >> ev)
		{
			//cout<< "\"" << ev << "\", ";
			record[t][i] = ev;
			i++;
			i_stream.ignore();
		}
		t++;
	}

	static const int gameNum = 81920;
	for(int i = 0; i < pnum; i++){
		parameter_cnt[i] = 0;
	}
	//Aに各盤面のパラメータの出現数を入れる
    for(int n = 1; n <= gameNum; n++)
    {
        Board c;
        for(int i = 0; i < 64; i++)
        {
            if(record[n][i] < INF)
            {
                int x = record[n][i] % 4;
                int y = 3 - (record[n][i] / 4);
                c.place(x, y);

                for(int p = 0; p <= pnum; p++)
                {
                    int ps[pnum]; //= {-60, -56, -16, 16, 56, 60, 30, 140, 11, 64, 16};//初期設定パラメータ
                    for(int i = 0; i < pnum; i++)
                    {
                        ps[i] = 0;
                    }
                    if (p < pnum) ps[p] = 1;
                    pb = ps[0], pc = ps[1], pd = ps[2], pe = ps[3];//基礎点
					pg = ps[4], ph = ps[5], pi = ps[6];//layer_me
					pj = ps[7], pk = ps[8], pl = ps[9];//leyer_you
					pm = ps[10], pn = ps[11], pr = ps[12], pt = ps[13];//intersection
					po = ps[14];//continuous
                    //pp = ps[17], pq = ps[18];//make T
					ppa = ps[15], ppb = ps[16], ppc = ps[17], ppd = ps[18];//makeT me
					pqa = ps[19], pqb = ps[20], pqc = ps[21], pqd = ps[22];//makeT you
					ppe = ps[23], ppf = ps[24], ppg = ps[25];//float_make me
					pqe = ps[26], pqf = ps[27], pqg = ps[28];//float_make you
                    A[n][i][p] = evaluate_pointsec_cont_layer_intersection(c);
					if((p < pnum) && (i < 18)){
						parameter_cnt[p] += abs(A[n][i][p]);
						// parameter_cnt[p] = min(parameter_cnt[p], 100);
					}
					
                }
                //定数項の影響を除く
                for(int p = 0; p < pnum; p++) A[n][i][p] -= A[n][i][pnum];
            }
        }
    }
	cout << "parameter_cnt = " << endl;
	for(int i = 0; i < pnum; i++){
		cout << parameter_cnt[i] << ",";
	}
	cout << endl;

	// int parameter[pnum]= {-104,-60,-20,26,78,62,312,234,198,64,542,-6,288,-180,634,266,790,112,14,16,-10,122,16,52,18};

	int threadNum = omp_get_max_threads();//ランダム初期値の生成回数
	// threadNum = 1;
	omp_set_num_threads(threadNum);
    cout << "number of thread = " << threadNum << endl;

	// 4 範囲分の結果を保存しておき、最後にまとめて表示する。
	int bestOneAll[rangeNum][pnum + 1] = {};
	long double bestOneLossAll[rangeNum] = {};

	//ここから 4 範囲を順番に回す
	for(int r = 0; r < rangeNum; r++)
	{
	const int rangeBegin = ranges[r].begin;
	const int rangeEnd   = ranges[r].end;

	cout << endl;
	cout << "==================================================" << endl;
	cout << "range[" << r << "] = " << ranges[r].label
	     << "  (for i = " << rangeBegin << "; i < " << rangeEnd << "; i = i + 2)" << endl;
	cout << "==================================================" << endl;

	long double bestloss[threadNum][pnum + 1];
    //ここから最急降下法
	# pragma omp parallel
	{
		int thread = omp_get_thread_num();
		long double loss;
		long double firstloss;
		// long double betterloss;
		bestloss[thread][pnum] = INF;

		uniform_int_distribution<int> dist(-1500, 1500);
		int random_parameter[pnum] = {};

		for(int i = 0; i < pnum; i++)random_parameter[i] = dist(rng);
		for(int i = 0; i < pnum; i++)cout << random_parameter[i] << ",";
		cout << endl;
		
		for(int t = 0; t < 40; t++)
		{
			bool flag = false;
			int conticnt[pnum] = {};//連続何回目かを入れる
			int contiflag[pnum] = {};//前回どの方向に進んだかを入れる
			for(int i = 0; i < pnum; i++)contiflag[i] = 2;//contiflag初期化
			firstloss = bestloss[thread][pnum];//firstloss初期化
			cout << "firstloss = " << firstloss ;
			cout << endl;
			
			for(int n = 0; n < 1000; n++)
			{	
				double differ[pnum] = {};
				for(int i = 0; i < pnum; i++)
				differ[i] = 0;
				loss = 0;
				for(int t = 1; t <= gameNum; t++)
				{
					//for(int i = 0; i < 64; i++)
					// 元ファイルでは下記 4 つのうち 1 つだけを有効にしていた箇所。
					// ここでは ranges[r] で範囲を切り替える。
					// for(int i = 4; i < 18; i = i + 2)//5~18
					// for(int i = 18; i < 32; i = i + 2)//19~32
					// for(int i = 32; i < 46; i = i + 2)//33~46
					// for(int i = 46; i < 60; i = i + 2)//47~60
					for(int i = rangeBegin; i < rangeEnd; i = i + 2)
					{
						if(record[t][i] < INF)
						{
							//if((i % 2 == 1) && (evaluatessec[t][(i - 1) >> 1] > -INF) && (evaluatessec[t][(i - 1) >> 1] < INF))
							if((evaluatesfir[t][i / 2] > -INF) && (evaluatesfir[t][i / 2] < INF))
							{
								//int training_old = evaluate_pointfir_layer_intersection(c);
								int training = A[t][i][pnum];
								for(int p = 0; p < pnum; p++) training += random_parameter[p] * A[t][i][p];
								//assert(training == training_old);
								long double p;//teacher
								long double q;
								
								if(evaluatesfir[t][i / 2] < -1840) p = 0.99;
								else if(evaluatesfir[t][i / 2] > 1840) p = 0.01;
								else p = 1 - 1/(1 + exp((long double) -evaluatesfir[t][i / 2]/400));
								if(training < -1840) q = 0.01;
								else if(training > 1840) q = 0.99;
								else q = 1/(1 + exp((long double)-(training)/400));
								/*long double p = 1 - 1/(1 + exp((long double)-(evaluatessec[t][(i - 1)/2] + 112)/200));
								long double q = 1/(1 + exp((long double)-(training)/200));
								if(q < 0.01) q = 0.01;
								else if(q > 0.99) q = 0.99;
								if(p < 0.01) p = 0.01;
								else if(p > 0.99) p = 0.99;*/
								//cout << "p=" << p << "," << "q=" << q << "," << training << endl;
								loss += -p*log(q) - (1 - p)*log1p(-q);
								//cout << "loss[" << i << "]=" << loss << endl;
								for(int j = 0; j < pnum; j++)
								{
									differ[j] += A[t][i][j]*(p-q);
								}
							}
						}
					}
				}
				//この時点でn回目の時のlossが求まる

				if(loss < bestloss[thread][pnum])
				{
					// cout << "(thread,t,n)=" << "(" << thread << "," << t << "," << n << ") ";
					//cout << "m = " << m << ", t = " << t << ", n = " << n << ",";
					for(int i = 0; i < pnum; i++)
					{
						bestloss[thread][i] = random_parameter[i];
						//cout << parameter[i] << ",";
						// cout << random_parameter[i] << ",";
					}
					//cout << "betterloss = " << betterloss << ",";
					// cout << "loss = " << loss << endl;
					// betterloss = loss;
					bestloss[thread][pnum] = loss;
				}

				{//途中経過を表示する
					// cout << "n = " << n << ",";
					// for(int i = 0; i < pnum; i++)
					// {
					// 	cout << random_parameter[i] << ",";
					// }
					// //cout << "betterloss = " << betterloss << ",";
					// cout << "loss = " << loss << endl;
				}

				int cnt = 0;
				
				for(int i = 0; i < pnum; i++)
				{
					/*if(i == 12 || i == 13 || i == 14 || i == 15)
					{
						if(differ[i] > 1) differ[i] = 1;
						else if(differ[i] < -1) differ[i] = -1;
						else
						{
							differ[i] = 0;
							cnt++;
						}
						parameter[i] = parameter[i] + differ[i];
					}
					else*/
					{
						if(differ[i] > 000 + pow((double)1.05, n)) //基本は9000+pow(1.15,n)
						{
							differ[i] = 1;
							if(contiflag[i] == 1)conticnt[i]++;
							else conticnt[i] = 0;
							contiflag[i] = 1;
						}
						else if(differ[i] < -000 - pow((double)1.05, n)) 
						{
							differ[i] = -1;
							if(contiflag[i] == -1)conticnt[i]--;
							else conticnt[i] = 0;
							contiflag[i] = -1;
						}
						else 
						{
							differ[i] = 0;
							conticnt[i] = 0;
							contiflag[i] = 0;
							cnt++;
						}
						//parameter[i] = parameter[i] + differ[i];
						random_parameter[i] = random_parameter[i] + differ[i] + conticnt[i];
					}
				}
				/*
				for(int i = 0; i < pnum; i++)
				{
					int add = differ[i] / 12656;
					parameter[i] = parameter[i] + add;
					if(add < 1 && add > -1) cnt++;
				}
				*/
				if(cnt == pnum) //収束判定
				{
					cout << "converge" << endl;
					if(firstloss - bestloss[thread][pnum] > 0.1)//次に行く
					{
						cout << "\033[31mrefined\033[m" << endl;
                        cout << "thread = " << thread << ", t = " << t << endl;
						for(int i = 0; i < pnum; i++)
						{
							// bestloss[thread][i] = random_parameter[i];
							//cout << parameter[i] << ",";
							// cout << random_parameter[i] << ",";
							random_parameter[i] = bestloss[thread][i];
						}
						// bestloss[thread][pnum] = betterloss;
						cout << "loss = " << bestloss[thread][pnum] << endl;
						break;
					}
					else//次に行かない
					{
						// cout << "NOT refined, loss = " << firstloss << endl;
						cout << "NOT refined, loss = " << bestloss[thread][pnum] << endl;
                        cout << "thread = " << thread << endl;
						// bestloss[thread][pnum] = betterloss;
						flag = true;
						break;
					}
					//"\033[31m(Black)\033[m";
					//return 0;
				}
				
				/*
				if(bestn == 0)
				betterloss = 2*loss;
				//betterloss = 134819;
				bestn = INF;
				if(loss <= betterloss)
				{
					cout << "n = " << n << ",";
					for(int i = 0; i < pnum; i++)
					{
						cout << ps[i] << ",";
					}
					//cout << "betterloss = " << betterloss << ",";
					cout << "loss = " << loss << endl;
					betterloss = loss;
					h = 0;
				}
				else
				{
					h++;
					if(h % 2000 == 0)cout << "n = " << n << "/" << pow(3, pnum) << endl;
				}
				//cout << "betterloss = " << betterloss << endl;
				*/
			}
			if(flag == true)break;
		}
	}

	int bestOne[pnum + 1];
	float bestOneLoss;
	for(int i = 0; i < pnum; i++){
		bestOne[i] = bestloss[0][i];
	}
	bestOne[pnum] = 0;
	bestOneLoss = bestloss[0][pnum];

	for(int m = 0; m < threadNum; m++)
	{
		cout << "thread = " << m << ",  ";
		for(int i = 0; i < pnum; i++)
		{
			cout << bestloss[m][i] << ",";
		}
		cout << "loss = " << bestloss[m][pnum];
		cout << endl;
		if(bestOneLoss > bestloss[m][pnum]){
			for(int i = 0; i < pnum; i++){
				bestOne[i] = bestloss[m][i];
			}
			bestOne[pnum] = m;
			bestOneLoss = bestloss[m][pnum];
		}
	}
	cout << endl;
	cout << "best thread = " << bestOne[pnum] << ",  ";
	cout << endl;
	for(int i = 0; i < pnum; i++){
		cout << bestOne[i] << ",";
	}
	cout << "loss = " << bestOneLoss;
	cout << endl;

	// 最後のまとめ表示用に保存する。
	for(int i = 0; i <= pnum; i++) bestOneAll[r][i] = bestOne[i];
	bestOneLossAll[r] = bestOneLoss;

	}//range ループここまで

	//ここから 4 範囲分のまとめ
	cout << endl;
	cout << "##################################################" << endl;
	cout << "#            全 4 範囲の結果まとめ               #" << endl;
	cout << "##################################################" << endl;
	for(int r = 0; r < rangeNum; r++)
	{
		cout << "range " << ranges[r].label << " : best thread = " << bestOneAll[r][pnum] << ",  ";
		for(int i = 0; i < pnum; i++) cout << bestOneAll[r][i] << ",";
		cout << "loss = " << bestOneLossAll[r] << endl;
	}
	cout << endl;

	return 0;

	//cout << "\"" << first_evaluate << "\"" << endl;
	
	/*
	int first_evaluates = stoi(first_evaluate);
	cout << first_evaluates;
	*/

	/*
	Board b;
	b.place(0,0);
	b.place(3,3);
	b.place(0,3);
    cout << evaluate_pointfir_cont_layer_intersection(b);
	*/
    
	

	HumanPlayer H;
	AIPlayer p1(1, evaluate_pointfir_cont_layer_intersection);
	AIPlayer p2(4, evaluate_pointsec_cont_layer_intersection);
	AIPlayer p3(9, evaluate_random);//全ランダム
	//p2.set_random(50);//一部ランダム
	Game game(&p1, &H, true, {});//ゲーム設定
	game.game();//連続で試合をする場合はここをコメントアウトする
	return 0;//連続で試合をする場合はここをコメントアウトする
	int cnt[3] = {};
	const int N =15000;//<=100000
	for (int t = 1; t<=N; t++)
	{
		if(t % sparse == 1 || t == N)
		cout << "Game #" << t << endl;
		Game game(&p1, &p2, false, {{0, 0}, {3, 3}, {0, 3}, {3, 0}});
		enum Color r = game.game();
		cnt[r]++;
		if(t % sparse == 0 || t == N)
		{
			cout << "Black : " << cnt[Color::Black] << endl;
			cout << "White : " << cnt[Color::White] << endl;
			cout << " Draw : " << cnt[Color::Draw] << endl;
		}
	}
	//std::string output_csv_file_path = "/yonmoku/parameter2.csv";
	//std::ofstream ofs_csv_file(output_csv_file_path );

	int countfir[3][500][32] = {};
	int countsec[3][500][32] = {};
	for(int t = 1; t <= N; t++)
	{
		for(int i = 1; i < 33; i++)
		{
			if(-500 <= evaluatesfir[t][i] && evaluatesfir[t][i] < 500)
			{
				countfir[evaluatesfir[t][0] + 1][(evaluatesfir[t][i] + 500)/2][(i + 1)/3]++;
			}
			if(-500 <= evaluatessec[t][i] && evaluatessec[t][i] < 500)
			{
				countsec[evaluatessec[t][0] + 1][(evaluatessec[t][i] + 500)/2][(i + 1)/3]++;	
			}
		}
	}
	//count[勝敗][評価関数 1刻み(-500 <= < 500)][turn]

	//勝率を求める(先手)
	double interest = 1.05;
	double sumfir = 0;
	double notzero = 0;
	for(int i = 0; i < 500; i++)
	{
		for(int k = 0; k < 32; k++)
		{
			double n = countfir[2][i][k] + countfir[1][i][k] + countfir[0][i][k];
			double rate;
			double estimate;
			double sigmoid;

			if(n != 0)
			{
				notzero = notzero + 1;
				rate = countfir[2][i][k]/n;
				sigmoid = 1/(1 + exp((double)-(2*i - 500 + 0.5)/200));
				//sumfir += (1/(double)N)*pow((log(1 + sigmoid) - log(1 + rate)),2);//平均二乗対数誤差
				sumfir += abs(rate - sigmoid)*(pow(interest, 3*k));//平均絶対誤差
				//sumfir += -rate*log(sigmoid) - (1 - rate)*log(1 - sigmoid);//交差エントロピー誤差
				//cout << n << " " << rate << " " << sigmoid << " " << log(1 + sigmoid) <<" " << log(1 + rate) << endl;
				//ofs_csv_file << rate << ',' << sigmoid << std::endl;
				//ofs_csv_file << countfir[2][i] << std::endl;
			}
		}
		
	}
	sumfir = (1/notzero)*sumfir;
	cout << notzero << endl;
	cout << "\033[31mfirst loss function is \033[m" << "\033[31m" << sumfir << "\033[m" << endl;

	sumfir = 0;
	notzero = 0;
	for(int i = 0; i < 500; i++)
	{
		for(int k = 0; k < 32; k++)
		{
			double n = countsec[2][i][k] + countsec[1][i][k] + countsec[0][i][k];
			double rate;
			double estimate;
			double sigmoid;

			if(n != 0)
			{
				notzero = notzero + 1;
				rate = countsec[2][i][k]/n;
				//sigmoid = 1/(1 + exp((double)-(5*i - 498)/200));
				sigmoid = 1/(1 + exp((double)-(2*i - 500 + 0.5)/200));
				//sumfir += (1/(double)N)*pow((log(1 + sigmoid) - log(1 + rate)),2);//平均二乗対数誤差
				sumfir += abs(rate - sigmoid)*(pow(interest, 3*k));//平均絶対誤差
				//cout << n << " " << rate << " " << sigmoid << " " << log(1 + sigmoid) <<" " << log(1 + rate) << endl;
				//ofs_csv_file << rate << ',' << sigmoid << std::endl;
			}
		}
		
	}
	sumfir = (1/notzero)*sumfir;
	cout << notzero << endl;
	cout << "second loss function is " << sumfir << endl;

	return 0;
}