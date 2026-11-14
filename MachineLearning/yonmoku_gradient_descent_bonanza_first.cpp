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
			if ((Me & LINES[i]) && (You & LINES[i])) ret[i] = 4;
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

int evaluate[LINES_NUM * (LINES_NUM - 1) / 2][64] = {};//[line * line][my stone * your stone]

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

		for(int i = 0; i < LINES_NUM * (LINES_NUM - 1) / 2; i++){
			for(int j = 0; j < 64; j++){
				evaluate[i][j] = 0;
			}
		}
		
		
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


// int A[100001][64][pnum + 1];
// int B[70000][64][LINES_NUM * (LINES_NUM - 1) / 2][64];
// int B[64][LINES_NUM * (LINES_NUM - 1) / 2][64];
uint8_t B[64][LINES_NUM * (LINES_NUM - 1) / 2];
int main()
{
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

	
    
	auto bonanza_2line = [&](const Board &board) -> int
	{
		int ret = 0;
		auto count = board.count();

		int t = 0;
		for(int i = 0; i < LINES_NUM; i++){
			for(int j = i + 1; j < LINES_NUM; j++){
				// if(i == j){
				// 	continue;
				// }
				// else{
					assert(t < LINES_NUM * (LINES_NUM - 1));
					assert(((count[i] + 3) * 8 + (count[j] + 3)) < 64);
					ret += evaluate[t][(count[i] + 3) * 8 + (count[j] + 3)];
					t++;
				// }
				
			}
		}
		return ret;
	};

	

    std::string input_first_evaluate = "/yonmoku/teacher/first_evaluate_ver7_1.csv";
	std::string input_second_evaluate = "/yonmoku/teacher/second_evaluate_ver7_1.csv";
	std::string input_record = "/yonmoku/teacher/record_ver7_1.csv";

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

	// std::string outputFile = "/yonmoku/feature.csv";
    // std::ofstream ofs_outputFile(outputFile);

	// static const int gameNum = 65536;
	static const int pnum = 64;
	static const int gameNum = 500;
	//Aに各盤面のパラメータの出現数を入れる
    // for(int n = 1; n <= gameNum; n++)
    // {
    //     Board c;
    //     for(int i = 0; i < 64; i++)
    //     {
    //         if(record[n][i] < INF)
    //         {
    //             int x = record[n][i] % 4;
    //             int y = 3 - (record[n][i] / 4);
    //             c.place(x, y);

    //             for(int p = 0; p <= pnum; p++)
    //             {
    //                 int ps[pnum]; //= {-60, -56, -16, 16, 56, 60, 30, 140, 11, 64, 16};//初期設定パラメータ
    //                 for(int i = 0; i < pnum; i++)
    //                 {
    //                     ps[i] = 0;
    //                 }
    //                 if (p < pnum) ps[p] = 1;
    //                 pb = ps[0], pc = ps[1], pd = ps[2], pe = ps[3];//基礎点
	// 				pg = ps[4], ph = ps[5], pi = ps[6];//layer_me
	// 				pj = ps[7], pk = ps[8], pl = ps[9];//leyer_you
	// 				pm = ps[10], pn = ps[11], pr = ps[12], pt = ps[13];//intersection
	// 				po = ps[14];//continuous
    //                 //pp = ps[17], pq = ps[18];//make T
	// 				ppa = ps[15], ppb = ps[16], ppc = ps[17], ppd = ps[18];//nonfloat_makeT me
	// 				pqa = ps[19], pqb = ps[20], pqc = ps[21], pqd = ps[22];//nonfloat_makeT you
	// 				ppe = ps[23], ppf = ps[24], ppg = ps[25];//float_make me
	// 				pqe = ps[26], pqf = ps[27], pqg = ps[28];//float_make you
    //                 A[n][i][p] = evaluate_pointfir_cont_layer_intersection(c);
    //             }
    //             //定数項の影響を除く
    //             for(int p = 0; p < pnum; p++) A[n][i][p] -= A[n][i][pnum];
				
    //         }
    //     }
    // }

	//Bに各盤面のパラメータの出現数を入れる
    // for(int n = 1; n <= gameNum; n++)
    // {
    //     Board c;
    //     for(int i = 0; i < 64; i++)
    //     {
    //         if(record[n][i] < INF)
    //         {
    //             int x = record[n][i] % 4;
    //             int y = 3 - (record[n][i] / 4);
    //             c.place(x, y);

	// 			int t = 0;
	// 			for(int k = 0; k < LINES_NUM; k++){
	// 				for(int l = k + 1; l < LINES_NUM; l++){
	// 					for(int p = 0; p < 64; p++){
	// 						evaluate[t][p] = 1;
	// 						B[n][i][t][p] = bonanza_2line(c);
	// 						evaluate[t][p] = 0;
	// 					}
	// 					t++;
	// 				}
	// 			}				
    //         }
    //     }
    // }

	//int parameter[pnum]= {-77,-65,-28,15,68,35,117,634,83,239,294,148,375,-163,928,0,599,346,2,69,19,7,39,34,15};

	
    int threadNum = omp_get_max_threads();//ランダム初期値の生成回数
	threadNum = 1;
	omp_set_num_threads(threadNum);
    cout << "number of thread = " << threadNum << endl;
	// long double bestloss[threadNum][pnum + 1];
	int best_parameter[threadNum][LINES_NUM * (LINES_NUM - 1) / 2][pnum];
	long double bestloss[threadNum];

	vector<int> line_of_cell[64];  // 各マスが属するラインのインデックス

	// 前処理（一度だけ）
	for(int cell = 0; cell < 64; cell++){
		unsigned long long bit = 1ULL << cell;
		for(int i = 0; i < LINES_NUM; i++){
			if(LINES[i] & bit) line_of_cell[cell].push_back(i);
		}
	}

    //ここから最急降下法
	# pragma omp parallel
    {
		int thread = omp_get_thread_num();
        long double loss;
        long double firstloss;
        bestloss[thread] = INF;

        uniform_int_distribution<int> dist(-500, 500);
		// int random_parameter[pnum] = {};
		cout << "OK" << endl;
		static thread_local int random_parameter[LINES_NUM * (LINES_NUM - 1) / 2][pnum] = {};
        
		// for(int i = 0; i < pnum; i++)random_parameter[i] = dist(rng);
		int t = 0;
		for(int i = 0; i < LINES_NUM; i++){
			for(int j = i + 1; j < LINES_NUM; j++){
				for(int p = 0; p < pnum; p++){
					random_parameter[t][p] = dist(rng);
					// random_parameter[t][p] = 0;
				}
				t++;				
			}
		}
		// for(int i = 0; i < pnum; i++)cout << random_parameter[i] << ",";
		// cout << endl;

		for(int t = 0; t < 50; t++)
		{
			bool flag = false;
			// int conticnt[pnum] = {};//連続何回目かを入れる
			// int contiflag[pnum] = {};//前回どの方向に進んだかを入れる
			static thread_local int conticnt[LINES_NUM * (LINES_NUM - 1) / 2][pnum] = {};//連続何回目かを入れる
			static thread_local int contiflag[LINES_NUM * (LINES_NUM - 1) / 2][pnum] = {};//前回どの方向に進んだかを入れる
			
			// for(int i = 0; i < pnum; i++)contiflag[i] = 2;//contiflag初期化
			int k = 0;
			for(int i = 0; i < LINES_NUM; i++){//contiflag初期化
				for(int j = i + 1; j < LINES_NUM; j++){
					for(int p = 0; p < pnum; p++){
						contiflag[k][p] = 2;
					}
					k++;				
				}
			}
			firstloss = bestloss[thread];//firstloss初期化
			cout << "firstloss = " << firstloss ;
			cout << endl;

			static thread_local double differ[LINES_NUM * (LINES_NUM - 1) / 2][pnum] = {};
			for(int n = 0; n < 1000; n++)
			{	
				// differ[LINES_NUM * (LINES_NUM - 1) / 2][64] = {};
				// for(int i = 0; i < pnum; i++)differ[i] = 0;
				int k = 0;
				for(int i = 0; i < LINES_NUM; i++){
					for(int j = i + 1; j < LINES_NUM; j++){
						for(int p = 0; p < pnum; p++){
							differ[k][p] = 0;
						}
						k++;				
					}
				}
				
				loss = 0;
				for(int game = 1; game <= gameNum; game++)
				{
					// cout << "game1 = " << game << endl;
					//Bに各盤面のパラメータの出現数を入れる
					// for(int l1 = 0; l1 < LINES_NUM * (LINES_NUM - 1) / 2; l1++){
					// 	for(int l2 = 0; l2 < 64; l2++){
					// 		evaluate[l1][l2] = 0;
					// 	}
					// }
					// cout << "game2 = " << game << endl;
					Board c;
					// array<int, LINES_NUM> cnt = {};  // 初期値0
					int cnt[LINES_NUM] = {};
					for(int i = 0; i < LINES_NUM; i++){
						cnt[i] = 0;
					}
					

					for(int i = 0; i < 64; i++)
					{
						if(record[game][i] < INF)
						{
							
							unsigned long long bit = c.Me | c.You;
							int x = record[game][i] % 4;
							int y = 3 - (record[game][i] / 4);
							c.place(x, y);

							unsigned long long place = (c.Me | c.You) & ~bit;
							int bit_pos = __builtin_ctzll(place);  // 一番右の1のビット位置を取得

							// bit_posに対応するラインだけ再計算
							for(int li : line_of_cell[bit_pos]){
								if((c.Me & LINES[li]) && (c.You & LINES[li])) cnt[li] = 4;
								else if(c.Me & LINES[li]) cnt[li] = __builtin_popcountll(c.Me & LINES[li]);
								else cnt[li] = -__builtin_popcountll(c.You & LINES[li]);
							}
							
							// auto count = c.count();

							int k = 0;
							for(int l1 = 0; l1 < LINES_NUM; l1++){
								for(int l2 = l1 + 1; l2 < LINES_NUM; l2++){
									int p = (cnt[l1] + 3) * 8 + (cnt[l2] + 3);
									B[i][k] = p;
									k++;
								}
							}				
						}
					}
					
					// cout << "game3 = " << game << endl;
					for(int i = 1; i < 64; i = i + 2)
					// for(int i = 3; i < 17; i = i + 2)//4~17
					// for(int i = 17; i < 31; i = i + 2)//18~31
					// for(int i = 31; i < 45; i = i + 2)//32~45
					// for(int i = 45; i < 59; i = i + 2)//46~59
					//for(int i = 43; i < 53; i = i + 2)//44~53
					{
						// assert(loss <= INF);
						if(record[game][i] < INF)
						{
							//if((i % 2 == 1) && (evaluatessec[t][(i - 1) >> 1] > -INF) && (evaluatessec[t][(i - 1) >> 1] < INF))
							if((evaluatessec[game][(i - 1) >> 1] > -INF) && (evaluatessec[game][(i - 1) >> 1] < INF))
							{
								//int training_old = evaluate_pointfir_layer_intersection(c);
								// int training = A[t][i][pnum];
								int training = 0;
								//for(int p = 0; p < pnum; p++) training += parameter[p] * A[t][i][p];
								// for(int p = 0; p < pnum; p++) training += random_parameter[p] * A[t][i][p];
								int k = 0;
								for(int l1 = 0; l1 < LINES_NUM; l1++){
									for(int l2 = l1 + 1; l2 < LINES_NUM; l2++){
										// for(int p = 0; p < 64; p++){
										// 	training += random_parameter[k][p] * B[i][k][p];
										// }
										if(B[i][k] == 27 || B[i][k] == 63){
											continue;
										}
										training += random_parameter[k][B[i][k]];
										k++;				
									}
								}

								//assert(training == training_old);
								long double p;
								long double q;
								
								if(evaluatessec[game][(i - 1)/2] < -1840) p = 0.99;
								else if(evaluatessec[game][(i - 1)/2] > 1840) p = 0.01;
								else p = 1 - 1/(1 + exp((long double)-(evaluatessec[game][(i - 1)/2])/400));
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
								// cout << "loss[" << i << "]=" << loss << endl;
								// for(int j = 0; j < pnum; j++)
								// {
								// 	differ[j] += A[t][i][j]*(p-q);
								// }
								k = 0;
								for(int l1 = 0; l1 < LINES_NUM; l1++){
									for(int l2 = l1 + 1; l2 < LINES_NUM; l2++){
										// for(int param = 0; param < 64; param++){
										// 	differ[k][param] += B[i][k][param]*(p-q);
										// }
										if(B[i][k] == 27 || B[i][k] == 63){
											continue;
										}
										differ[k][B[i][k]] += (p - q);
										assert(differ[k][27] == 0);
										assert(differ[k][63] == 0);
										k++;				
									}
								}
							}
						}
					}
				}
				//この時点でn回目の時のlossが求まる


				
				if(loss < bestloss[thread])
				{
					// cout << "(thread,t,n)=" << "(" << thread << "," << t << "," << n << ") ";
					//cout << "m = " << m << ", t = " << t << ", n = " << n << ",";
					// for(int i = 0; i < pnum; i++)
					// {
					// 	bestloss[thread][i] = random_parameter[i];
					// 	//cout << parameter[i] << ",";
					// 	// cout << random_parameter[i] << ",";
					// }

					int k = 0;
					for(int i = 0; i < LINES_NUM; i++){
						for(int j = i + 1; j < LINES_NUM; j++){
							for(int param = 0; param < pnum; param++){
								best_parameter[thread][k][param] = random_parameter[k][param];
							}
							k++;				
						}
					}
					//cout << "betterloss = " << betterloss << ",";
					// cout << "loss = " << loss << endl;
					// betterloss = loss;
					bestloss[thread] = loss;

					// cout << "best_parameter[0][0][0] = " << best_parameter[0][0][0] << endl;
    				// cout << "best_parameter[0][0][1] = " << best_parameter[0][0][1] << endl;
    				// cout << "best_parameter[0][0][2] = " << best_parameter[0][0][2] << endl;
    				// cout << "best_parameter[0][0][3] = " << best_parameter[0][0][3] << endl;
    				// cout << "best_parameter[0][0][4] = " << best_parameter[0][0][4] << endl;
				}

				{//途中経過を表示する
					cout << "n = " << n << ",";
					// for(int i = 0; i < pnum; i++)
					// {
					// 	cout << random_parameter[i] << ",";
					// }
					// //cout << "betterloss = " << betterloss << ",";
					// cout << "random_parameter[0][27] = " << random_parameter[0][27] << endl;
    				// cout << "random_parameter[0][63] = " << random_parameter[0][63] << endl;
    				// cout << "random_parameter[0][2] = " << random_parameter[0][2] << endl;
    				// cout << "random_parameter[0][3] = " << random_parameter[0][3] << endl;
    				// cout << "random_parameter[0][4] = " << random_parameter[0][4] << endl;
					cout << "loss = " << loss << endl;
				}

				int cnt = 0;

				k = 0;
				for(int i = 0; i < LINES_NUM; i++){
					for(int j = i + 1; j < LINES_NUM; j++){
						for(int param = 0; param < pnum; param++){
							assert(differ[k][27] == 0);
							assert(differ[k][63] == 0);
							if(differ[k][param] > 000 + pow((double)1.05, n))//基本は9000+pow(1.15,n)1.05
							// if(differ[k][param] > 9000 + pow((double)1.5, n))//基本は9000+pow(1.15,n)1.05
							{
								differ[k][param] = 1;
								if(contiflag[k][param] == 1)conticnt[k][param]++;
								else conticnt[k][param] = 0;
								contiflag[k][param] = 1;
							}
							else if(differ[k][param] < -000 - pow((double)1.05, n)) 
							// else if(differ[k][param] < -9000 - pow((double)1.5, n)) 
							{
								differ[k][param] = -1;
								if(contiflag[k][param] == -1)conticnt[k][param]--;
								else conticnt[k][param] = 0;
								contiflag[k][param] = -1;
							}
							else 
							{
								differ[k][param] = 0;
								conticnt[k][param] = 0;
								contiflag[k][param] = 0;
								cnt++;
								//正則化
								if(random_parameter[k][param] > 0){
									random_parameter[k][param]--;
								}
								else if(random_parameter[k][param] < 0){
									random_parameter[k][param]++;
								}
							}
							//parameter[i] = parameter[i] + differ[i];
							//assert(contiflag[i] == -1 || contiflag[i] == 0 || contiflag[i] == 1);
							random_parameter[k][param] = random_parameter[k][param] + differ[k][param] + conticnt[k][param];
						}
						k++;				
					}
				}
				
				if(cnt == (LINES_NUM * (LINES_NUM - 1) / 2) * pnum) //収束判定
				{
					cout << "converge" << endl;
					if(firstloss - bestloss[thread] > 0.1)//次に行く
					{
						cout << "\033[31mrefined\033[m" << endl;
                        cout << "thread = " << thread << ", t = " << t << endl;
						// for(int i = 0; i < pnum; i++)
						// {
						// 	// bestloss[thread][i] = random_parameter[i];
						// 	//cout << parameter[i] << ",";
						// 	// cout << random_parameter[i] << ",";
						// 	random_parameter[i] = bestloss[thread][i];
						// }

						int k = 0;
						for(int i = 0; i < LINES_NUM; i++){
							for(int j = i + 1; j < LINES_NUM; j++){
								for(int param = 0; param < pnum; param++){
									random_parameter[k][param] = best_parameter[thread][k][param];
								}
								k++;				
							}
						}

						// bestloss[thread][pnum] = betterloss;
						cout << "loss = " << bestloss[thread] << endl;
						break;
					}
					else//次に行かない
					{
						// cout << "NOT refined, loss = " << firstloss << endl;
						cout << "NOT refined, loss = " << bestloss[thread] << endl;
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
	
	// int bestOne[pnum + 1];
	int bestOne_parameter[LINES_NUM * (LINES_NUM - 1) / 2][pnum];
	int best_thread = 0;
	long double bestOneLoss;
	// for(int i = 0; i < pnum; i++){
	// 	bestOne[i] = bestloss[0][i];
	// }

	std::string feature;
	std::ofstream ofs_feature;

	feature = "/yonmoku/feature/feature.csv";
	ofs_feature.open(feature);

	int k = 0;
	for(int i = 0; i < LINES_NUM; i++){
		for(int j = i + 1; j < LINES_NUM; j++){
			for(int param = 0; param < pnum; param++){
				bestOne_parameter[k][param] = best_parameter[0][k][param];	
			}
			k++;				
		}
	}

	bestOneLoss = bestloss[0];

	for(int m = 0; m < threadNum; m++)
	{
		cout << "thread = " << m << ",  ";
		// for(int i = 0; i < pnum; i++)
		// {
		// 	cout << bestloss[m][i] << ",";
		// }
		cout << "loss = " << bestloss[m];
		cout << endl;
		if(bestOneLoss > bestloss[m]){
			// for(int i = 0; i < pnum; i++){
			// 	bestOne[i] = bestloss[m][i];
			// }

			int k = 0;
			for(int i = 0; i < LINES_NUM; i++){
				for(int j = i + 1; j < LINES_NUM; j++){
					for(int param = 0; param < pnum; param++){
						bestOne_parameter[k][param] = best_parameter[m][k][param];
					}
					k++;				
				}
			}

			best_thread = m;
			bestOneLoss = bestloss[m];
		}
	}

	// ofs_featureへの書き込み直前に追加
cout << "bestOne_parameter[0][0] = " << bestOne_parameter[0][0] << endl;
cout << "bestOne_parameter[1][0] = " << bestOne_parameter[1][0] << endl;

	k = 0;
	for(int i = 0; i < LINES_NUM; i++){
		for(int j = i + 1; j < LINES_NUM; j++){
			for(int param = 0; param < pnum; param++){
				ofs_feature << bestOne_parameter[k][param] << ",";
			}
			ofs_feature << std::endl;
			k++;				
		}
	}

	cout << endl;
	cout << "best thread = " << best_thread << ",  ";
	cout << endl;
	// for(int i = 0; i < pnum; i++){
	// 	cout << bestOne[i] << ",";
	// }
	cout << "loss = " << bestOneLoss;
	cout << endl;
	
	
	return 0;
	
	
}