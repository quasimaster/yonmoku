#pragma once

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
# include <stdio.h>

using namespace std;

inline mt19937 rng(random_device{}());
// inline mt19937 rng;
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

inline array<unsigned long long, LINES_NUM> LINES;
inline constexpr unsigned long long move_order[] = {
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
