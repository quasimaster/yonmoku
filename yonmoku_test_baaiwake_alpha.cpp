#include<iostream>
#include<queue>
#include<vector>
#include<array>
#include<algorithm>
#define NDEBUG
#include<cassert>
#include<random>
#include<set>
#include<map>
#include<chrono>
#include<string>
#include<fstream>
#include<sstream>
# include <stdio.h>
# include <omp.h> 

using namespace std;

mt19937 rng(random_device{}());
// mt19937 rng;
enum Cell{None, Me, You};
enum State{Continue, End, Invalid};
enum Color{Draw, Black, White};

static const int SIZE = 4;
#define IDX(x, y, z) ((x) + (y) * SIZE + (z) * SIZE * SIZE)
#define BIT(x, y, z) (1uLL << IDX(x, y, z))
#define X(idx) ((idx) % SIZE)
#define Y(idx) ((idx) / SIZE % SIZE)
#define Z(idx) ((idx) / SIZE / SIZE)
static const int BOARD_SIZE = SIZE * SIZE * SIZE;
static const int INF = 1e9;
static const int LINES_NUM = 76;

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

//static const int sparse = 1;
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
		cout << "    z=1  z=2  z=3  z=4\n";
		for (int y = SIZE - 1; y >= 0; y--)
		{
			cout << "y=" << y + 1 << " ";
			for (int z = 0; z < SIZE; z++)
			{
				for (int x = 0; x < SIZE; x++)
				{
					const unsigned long long bit = BIT(x, y, z);
					{
						if (black & bit) cout << "\033[31mX\033[m";
						else if (white & bit) cout << "O";
						else cout << "-";
					}
				}
				if (z + 1 < SIZE) cout << " ";
			}
			cout << "\n";
		}
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

	Board place_fast_clone(unsigned long long bit) const
	{
		Board b = *this;
		b.Me |= bit;
		swap(b.Me, b.You);
		return b;
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
				// int ev = -evaluate_board(b,level - 1, -INF , -mx + 1);
				// int ev = -evaluate_board(b,turn>=46?14:turn>=39?9:level - 1, -INF , -mx + 1);
				// int ev = -evaluate_board(b,turn>=44?16::level - 1, -INF , -mx + 1);//教師データ用ver3
                // int ev = -evaluate_board(b,turn>=43?17:turn>=35?9:level - 1, -INF , -mx + 1);//教師データ用ver4,シグモイド関数の係数は920
				// int ev = -evaluate_board(b,turn>=40?21:turn>=33?11:turn>=25?9:level - 1, -INF , -mx + 1);//教師データ用ver5,シグモイド関数の係数は1840
				// int ev = -evaluate_board(b,turn>=39?22:turn>=31?11:turn>=23?9:level - 1, -INF , -mx + 1);//教師データ用ver6,シグモイド関数の係数は1840
				int ev = -evaluate_board(b,turn>=37?24:turn>=29?11:turn>=21?9:level - 1, -INF , -mx + 1);//教師データ用ver7,シグモイド関数の係数は1840
                // int ev = -evaluate_board(b,turn>=39?21:turn>=37?12:turn>=29?10:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				// int ev = -evaluate_board(b,turn>=39?21:turn>35?13:turn>=29?11:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
				// int ev = -evaluate_board(b,turn>=39?22:turn>=33?13:turn>=21?11:level - 1, -INF , -mx + 1);//この行で途中からの読み手数を変更できる
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

int main()
{
	{
		vector<unsigned long long> lines;
		// lines.reserve(LINES_NUM);  
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

	auto evaluate_pointfir = [&](const Board &board, unsigned long long rMe, unsigned long long rYou) -> int
	{
		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		if(turn >= 60){
			return 0;
		}

		int sum = 0;
		static const int stdweight[28] = {
			0,-58,-20,0,27,57,0,
			0,-58,-20,0,27,57,0,
			0,-86,-9,0,22,56,0,
			0,-96,-31,-10,29,0
		};
		auto count = board.count();
		const int turn_bucket = (turn - 4) / 14;
		for (int v : count){
			assert(v >= -3 && v <= 3);
			sum += stdweight[turn_bucket * 7 + v + 3];//0~4,5~14,...,45~54 
		}

		static const int maketweight[32] = {
			-80,-38,45,0,5,-33,26,14,
			117,-62,68,27,52,-58,38,14,
			179,-53,120,78,109,-18,44,30,
			287,-176,139,100,248,-17,48,20
		};

		static const int conti_maketweight[24] = {
			109,143,384,66,119,174,
			203,252,52,80,101,64,
			362,648,100,135,294,28,
			689,1192,84,304,518,-169
		};

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
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
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
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket *8 + 4];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket *8 + 5];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket *8 + 6];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket *8 + 7];

					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
					floatthree ^= h;
				}
				
			}
            
		}
		sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 0];//T_T
		sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 1];//T_W
		sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 2];//W_T
		
		sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 3];
		sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 4];
		sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 5];
        return sum;

	};
	auto evaluate_pointsec = [&](const Board &board, unsigned long long rMe, unsigned long long rYou) -> int
	{
		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		if(turn >= 60){
			return 0;
		}
		int sum = 0;
		static const int weight[28] = {
			0,-52,-22,0,28,65,0,
			0,-70,-24,0,30,99,0,
			0,-33,-5,0,20,97,0,
			0,-2,11,0,27,122,0
		};
		
		auto count = board.count();
		const int turn_bucket = (turn - 5) / 14;
		for (int v : count){
			assert(v >= -3 && v <= 3);
			sum += weight[turn_bucket * 7 + v + 3];//1~3,4~13,...,44~53
		} 
		static const int maketweight[32] = {
			8,-56,25,1,105,-12,44,20,
			30,-47,34,7,112,-49,65,39,
			79,-27,54,30,206,-57,126,84,
			516,-93,33,0,424,-161,123,89
		};

		static const int conti_maketweight[24]{
			85,90,100,72,110,345,
			78,98,14,171,206,101,
			135,312,-4,421,694,139,
			317,427,-268,861,1411,188
		};

		static const unsigned long long mask_1 = 0x000000000000ffffuLL;
		static const unsigned long long mask_2 = 0x00000000ffff0000uLL;
		static const unsigned long long mask_3 = 0x0000ffff00000000uLL;
		static const unsigned long long mask_4 = 0xffff000000000000uLL;
        unsigned long long tMe = 0uLL;
        unsigned long long tYou = 0uLL;
		for(int i = 0; i < LINES_NUM; i++)
		{
			if(count[i] == 2)
			{
				unsigned long long two = ~board.Me & LINES[i];//LINE内の玉が入っていない部分
				unsigned long long floatthree = two & mask_3 & ~((rYou | board.Me | board.You) << SIZE * SIZE);//twoのうち、浮き3段目決勝点の候補
				while(floatthree)
				{
					unsigned long long h = floatthree & -floatthree;
					unsigned long long make = two & ~h;//makeT点
                    tMe |= make;
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 0];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 1];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 2];
					sum += __builtin_popcountll(make & ~(rYou >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 3];

					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 0];//two
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 1];//three
					// sum += __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 2];//four
					floatthree ^= h;
				}
			}
			else if(count[i] == -2)
			{
				unsigned long long two = ~board.You & LINES[i];
				unsigned long long floatthree = two & mask_3 & ~((rMe | board.Me | board.You) << SIZE * SIZE);
				while(floatthree)
				{
					unsigned long long h = floatthree & -floatthree;
					unsigned long long make = two & ~h;
                    tYou |= make;
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_1) * maketweight[turn_bucket * 8 + 4];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_2) * maketweight[turn_bucket * 8 + 5];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_3) * maketweight[turn_bucket * 8 + 6];
					sum -= __builtin_popcountll(make & ~(rMe >> SIZE*SIZE) & mask_4) * maketweight[turn_bucket * 8 + 7];

					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_2) * float_maketweight[turn_bucket * 6 + 3];//two
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_3) * float_maketweight[turn_bucket * 6 + 4];//three
					// sum -= __builtin_popcountll(float_make & ~(rYou >> SIZE*SIZE) & mask_4) * float_maketweight[turn_bucket * 6 + 5];//four
					floatthree ^= h;
				}
			}
            
		}
		sum += __builtin_popcountll(tMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 0];//T_T
		sum += __builtin_popcountll(rMe & tMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 1];//T_W
		sum += __builtin_popcountll(tMe & rMe << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 2];//W_T
		
		sum -= __builtin_popcountll(tYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 3];
		sum -= __builtin_popcountll(rYou & tYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 4];
		sum -= __builtin_popcountll(tYou & rYou << SIZE * SIZE) * conti_maketweight[turn_bucket * 6 + 5];
        return sum;
	};
	auto evaluate_random = [](const Board &board) -> int
	{
		return 0;
	};
	auto continuous_fir = [](const Board &board, unsigned long long rMe, const unsigned long long rYou) -> int
	{
		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		if(turn >= 60){
			return 0;
		}
		rMe &= ~(rYou << SIZE * SIZE);
		static const int parameter[4] = {860,1034,649,527};
		//assert(turn < 64);
		return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[(turn - 4) / 14];
	};
	auto continuous_sec = [](const Board &board, unsigned long long rMe, const unsigned long long rYou) -> int
	{
		const int turn = board.turn();// turn number (the number of stones = turn - 1)
		if(turn >= 60){
			return 0;
		}
		rMe &= ~(rYou << SIZE * SIZE);
		static const int parameter[4] = {1158,1037,707,657};
		return __builtin_popcountll(rMe & rMe << SIZE * SIZE) * parameter[(turn - 5) / 14];
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

		if(turn >= 60){
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
			return sum;
		}

        static const int weightfir[40] = {
			125,484,129,185,228,181,136,583,1342,1157,
            166,579,149,297,357,224,318,290,565,-1018,
            156,881,89,318,634,238,492,454,1114,-575,
            190,1515,109,448,1001,316,1097,637,1989,1031
        };
        static const int weightsec[40] = {
            230,235,178,141,451,148,307,1356,208,-809,
            310,387,233,174,537,159,271,296,1504,-181,
            292,719,230,151,916,88,543,445,1029,235,
            491,1305,365,157,1434,58,1083,1036,1630,-1088
        };

		if (now == Color::Black)
		{//first (black) player
			{//Me, first (black) player
				sum += __builtin_popcountll(rMe & mask_2) * weightfir[((turn - 4) / 14)*10 + 0];//2nd layer_intersection_fir
				sum += __builtin_popcountll(rMe & mask_3) * weightfir[((turn - 4) / 14)*10 + 1];//3rd layer_intersection_fir
				sum += __builtin_popcountll(rMe & mask_4) * weightfir[((turn - 4) / 14)*10 + 2];//4th layer_intersection_fir
			}
			{//You, second (white) player
				sum -= __builtin_popcountll(rYou & mask_2) * weightfir[((turn - 4) / 14)*10 + 3];//2nd layer_intersection_fir
				sum -= __builtin_popcountll(rYou & mask_3) * weightfir[((turn - 4) / 14)*10 + 4];//3rd layer_intersection_fir
				sum -= __builtin_popcountll(rYou & mask_4) * weightfir[((turn - 4) / 14)*10 + 5];//4th layer_intersection_fir
			}
			if (intersection_3)
			{//if there exists intersections of reaches on 3rd layer
				int intersection = __builtin_popcountll(intersection_3);
				//assert(intersection < 5);
				//if (__builtin_parityll(intersection_3))
				if(intersection == 1)
				{//odd, black = Me
					sum += weightfir[((turn - 4) / 14)*10 + 6];
				}
				else if(intersection == 2)
				{//even, white = You
					sum -= weightfir[((turn - 4) / 14)*10 + 7];
				}
				else if(intersection == 3)
				sum += weightfir[((turn - 4) / 14)*10 + 8];
				else if(intersection == 4)
				sum -= weightfir[((turn - 4) / 14)*10 + 9];
			}
		}
		else
		{//second (white) player
			{//Me, second (white) player
				sum += __builtin_popcountll(rMe & mask_2) * weightsec[((turn - 5) / 14)*10 + 0];//2nd layer_intersection_sec
				sum += __builtin_popcountll(rMe & mask_3) * weightsec[((turn - 5) / 14)*10 + 1];//3rd layer_intersection_sec
				sum += __builtin_popcountll(rMe & mask_4) * weightsec[((turn - 5) / 14)*10 + 2];//4th layer_intersection_sec
			}
			{//You, first (black) player
				sum -= __builtin_popcountll(rYou & mask_2) * weightsec[((turn - 5) / 14)*10 + 3];//2nd layer_intersection_sec
				sum -= __builtin_popcountll(rYou & mask_3) * weightsec[((turn - 5) / 14)*10 + 4];//3rd layer_intersection_sec
				sum -= __builtin_popcountll(rYou & mask_4) * weightsec[((turn - 5) / 14)*10 + 5];//4th layer_intersection_sec
			}
			if (intersection_3)
			{//if there exists intersections of reaches on 3rd layer
				int intersection = __builtin_popcountll(intersection_3);
				if (intersection == 1)
				{//odd, black = You
					sum -= weightsec[((turn - 5) / 14)*10 + 6];
				}
				else if(intersection == 2)
				{//even, white = Me
					sum += weightsec[((turn - 5) / 14)*10 + 7];
				}
				else if(intersection == 3)
				sum -= weightsec[((turn - 5) / 14)*10 + 8];
				else if(intersection == 4)
				sum += weightsec[((turn - 5) / 14)*10 + 9];
			}
		}
		return sum;
	};
	auto evaluate_pointfir_cont_layer_intersection = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointfir(board, rMe, rYou) + continuous_fir(board, rMe, rYou) - continuous_fir(board, rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
	};
	auto evaluate_pointsec_cont_layer_intersection = [&](const Board &board) -> int
	{
		const enum Color now = board.player();
		const unsigned long long rMe = Board::reach(board.Me) & ~board.You;
		const unsigned long long rYou = Board::reach(board.You) & ~board.Me;
		const unsigned long long hand = board.valid_move();
		return evaluate_pointsec(board, rMe, rYou) + continuous_sec(board, rMe, rYou) - continuous_sec(board, rYou, rMe) + reach_layer_intersection(board,now, rMe, rYou, hand);
	};

	HumanPlayer H;
	AIPlayer p1(8, evaluate_pointfir_cont_layer_intersection);
	AIPlayer p2(8, evaluate_pointsec_cont_layer_intersection);
	AIPlayer p3(6, evaluate_random);//全ランダム
	AIPlayer p4(6, evaluate_random);//全ランダム
	// p1.set_random(10);
	// p2.set_random(10);//一部ランダム
	Game game(&H, &p2, true, {{0,0}, {3,3}, {3,0},{0,3},{0,0},{3,3}});//ゲーム設定
	p1.set_game(&game);
	p2.set_game(&game);
	game.game();//連続で試合をする場合はここをコメントアウトする
	return 0;//連続で試合をする場合はここをコメントアウトする
	int cnt[3] = {};
	static const int N = 4096;//<=100000 4096 8192

	//return 0;
	
	// std::string output_first_evaluate = "/yonmoku/first_evaluate_ver5_esc.csv";
	// std::string output_second_evaluate = "/yonmoku/second_evaluate_ver5_esc.csv";
	// std::string output_record= "/yonmoku/record_ver5_esc.csv";

	// std::ofstream ofs_first_evaluate(output_first_evaluate);
	// std::ofstream ofs_second_evaluate(output_second_evaluate);
	// std::ofstream ofs_record(output_record);

	cout << "max_threads : " <<  omp_get_max_threads() << endl;
	static const int setting = 8;//使用するスレッド数
	omp_set_num_threads(setting);

	

	std::string output_first[setting];
	std::string output_second[setting];
	std::string output_records[setting];

	std::ofstream ofs_first[setting];
	std::ofstream ofs_second[setting];
	std::ofstream ofs_records[setting];

	for(int i = 0; i < setting; i++){
		output_first[i] = "/yonmoku/esc/first_evaluate_ver6_esc_thread" + std::to_string(i) + ".csv";
		output_second[i] = "/yonmoku/esc/second_evaluate_ver6_esc_thread" + std::to_string(i) + ".csv";
		output_records[i] = "/yonmoku/esc/record_ver6_esc_thread" + std::to_string(i) + ".csv";
	}
	for(int i = 0; i < setting; i++){
		ofs_first[i].open(output_first[i]);
		ofs_second[i].open(output_second[i]);
		ofs_records[i].open(output_records[i]);
	}

	std::string log;
	std::ofstream ofs_log;

	log = "/yonmoku/esc/log.csv";
	ofs_log.open(log);

	static const bool display = false;//表示の変更
	static const int start[4] = {0, 1, 2, 3}; 
	int gameNum[setting];
	

	static const int start_num[setting] = {4096,4096,4096,3920,4096,4096,4096,4096};
	for(int i = 0; i < setting; i++){
		gameNum[i] = start_num[i];
	}
	int start_sum = 0;
	for(int i = 0; i < setting; i++){
		start_sum += start_num[i];
	}
	# pragma omp parallel private(rng)
	{
		int thread = omp_get_thread_num();
		for(int t = start_num[thread]; t < N; t++)
		{
			AIPlayer p1(8, evaluate_pointfir_cont_layer_intersection);
			AIPlayer p2(8, evaluate_pointsec_cont_layer_intersection);
			p1.set_random(10);
			p2.set_random(10);//一部ランダム

			// cout << "Game #" << t  << endl;
			Game game(&p1, &p2, display, {{start[t % 4], start[(t / 4) % 4]}, {start[(t / 16) % 4], start[(t / 64) % 4]}, 
											{start[(t / 256) % 4], start[(t / 1024) % 4]}});
			p1.set_game(&game);
        	p2.set_game(&game);
			enum Color r = game.game();
			cnt[r]++;
			gameNum[thread]++;
			cout << "thread = " << thread << endl;
			cout << "Black : " << cnt[Color::Black] << endl;
			cout << "White : " << cnt[Color::White] << endl;
			cout << " Draw : " << cnt[Color::Draw] << endl;
			cout << "each thread ";
			for(int i = 0; i < setting; i++){
				cout << gameNum[i] << ",";
			}
			cout << "times game have finished" << endl;
			cout << (cnt[Color::Black] + cnt[Color::White] + cnt[Color::Draw] + start_sum) * 100 / (double)(N * setting) << " % has finished" << endl;
			for(int i = 0; i < setting; i++){
				ofs_log << gameNum[i] << ",";
			}
			ofs_log << std::endl;
			for(int i = 1; i < 33; i++)
			{
				ofs_first[thread] << game.evaluatesfir_tmp[i] << ",";
			}
			ofs_first[thread] << std::endl;
			for(int i = 1; i < 33; i++)
			{
				ofs_second[thread] << game.evaluatessec_tmp[i] << ",";
			}
			ofs_second[thread] << std::endl;
			for(int i = 0; i < 64; i++)
			{
				ofs_records[thread] << game.record_tmp[i] << ",";
			}
			ofs_records[thread] << std::endl;
			// #pragma omp barrier
		}
	}
	return 0;
	// for(int t = 0; t < N; t++)
	// {
	// 	//if(t % sparse == 1 || t == N || sparse == 1)
	// 	{
	// 		cout << "Game #" << t << endl;
	// 	}
	// 	Game game(&p1, &p2, display, {{start[t % 4], start[(t / 4) % 4]}, {start[(t / 16) % 4], start[(t / 64) % 4]}, 
	// 									{start[(t / 256) % 4], start[(t / 1024) % 4]}});
	// 	enum Color r = game.game();
	// 	cnt[r]++;
	// 	//if(t % sparse == 0 || t == N)
	// 	{
	// 		cout << "Black : " << cnt[Color::Black] << endl;
	// 		cout << "White : " << cnt[Color::White] << endl;
	// 		cout << " Draw : " << cnt[Color::Draw] << endl;
	// 	}
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_first_evaluate << evaluatesfir[t][i] << ",";
	// 		ofs_first_evaluate << game.evaluatesfir_tmp[i] << ",";
	// 	}
	// 	ofs_first_evaluate << std::endl;
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_second_evaluate << evaluatessec[t][i] << ",";
	// 		ofs_second_evaluate << game.evaluatessec_tmp[i] << ",";
	// 	}
	// 	ofs_second_evaluate << std::endl;
	// 	for(int i = 0; i < 64; i++)
	// 	{
	// 		//ofs_record << record[t][i] << ",";
	// 		ofs_record << game.record_tmp[i] << ",";
	// 	}
	// 	ofs_record << std::endl;
	// }

	// return 0;
	// //std::string output_csv_file_path = "/yonmoku/parameter2.csv";
	// //std::ofstream ofs_csv_file(output_csv_file_path );

	// for(int t = 1; t <= N; t++)
	// {
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_first_evaluate << evaluatesfir[t][i] << ",";
	// 		ofs_first_evaluate << game.evaluatesfir_tmp[i] << ",";
	// 	}
	// 	ofs_first_evaluate << std::endl;
	// 	for(int i = 1; i < 33; i++)
	// 	{
	// 		//ofs_second_evaluate << evaluatessec[t][i] << ",";
	// 		ofs_second_evaluate << game.evaluatessec_tmp[i] << ",";
	// 	}
	// 	ofs_second_evaluate << std::endl;
	// 	for(int i = 0; i < 64; i++)
	// 	{
	// 		//ofs_record << record[t][i] << ",";
	// 		ofs_record << game.record_tmp[i] << ",";
	// 	}
	// 	ofs_record << std::endl;
	// }

	return 0;
}
