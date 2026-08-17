#ifndef USE_ASSERT
#define NDEBUG          // ← すべての #include より前(assert 無効化。-DUSE_ASSERT で有効化)
#endif

// 最終盤の厳密評価(段パリティ規則 R2 + ゲート付き厳密打ち切り)のベンチマーク用ハーネス。
// 設計: docs/設計書/最終盤/implementation-plan-endgame-exact.md §5.4
//
// main_alpha_pvs_eval_inc_tbl_id.cpp は先頭が「人間 vs AI 対局」モードで計時に使えないため、
// 同じ AI・同じ評価関数で AI vs AI の自己対戦だけを回す最小ハーネスを別に用意する。
// 探索・評価・盤面・TT は main_alpha_pvs_eval_inc_tbl_id.cpp と完全に同一のものを include する。
//
//   引数: [対局数] [読み手数 level]     既定 = 8 局 / level 10(= 既存 main と同じ)
//   出力: 対局ごとの 手数 / 勝敗 / 秒 / ノード数 と、その合計
//
// ビルド(比較は必ず同一フラグで):
//   g++ -std=c++17 -O2 -DBENCH -DUSE_ENDGAME_R2=0 -DUSE_ENDGAME_CUT=0 code/bench_endgame_selfplay.cpp -o bench_off
//   g++ -std=c++17 -O2 -DBENCH -DUSE_ENDGAME_R2=1 -DUSE_ENDGAME_CUT=0 code/bench_endgame_selfplay.cpp -o bench_r2
//   g++ -std=c++17 -O2 -DBENCH -DUSE_ENDGAME_R2=1 -DUSE_ENDGAME_CUT=1 code/bench_endgame_selfplay.cpp -o bench_eg

#ifndef USE_ENDGAME_R2
#define USE_ENDGAME_R2 1
#endif
#ifndef USE_ENDGAME_CUT
#define USE_ENDGAME_CUT 1
#endif

#include "common.hpp"
#include "board.hpp"
#include "player.hpp"
#include "game.hpp"
#include "tt.hpp"
#include "board_inc.hpp"
#include "ai_player_pvs_inc_id.hpp"
#include "evaluate_alpha_inc_tbl.hpp"
using AI = AIPlayerPVSIncID<int(*)(const BoardInc&, unsigned long long, unsigned long long, unsigned long long)>;

// 定跡(重複なし初手列)。main_alpha_pvs_eval_inc_tbl_id.cpp の load_openings と同一。
static vector<vector<pair<int, int> > > load_openings(const string& rel_path)
{
	static const char* prefix[] = {"", "../", "../../"};
	ifstream ifs;
	string used;
	for(const char* p : prefix)
	{
		used = string(p) + rel_path;
		ifs.open(used);
		if(ifs) break;
		ifs.clear();
	}
	if(!ifs) { cerr << "openings file not found: " << rel_path << endl; return {}; }

	vector<vector<pair<int, int> > > openings;
	string line;
	while(getline(ifs, line))
	{
		size_t head = line.find_first_not_of(" \t");
		if(head == string::npos || line.compare(head, 2, "{{") != 0) continue;
		vector<int> nums;
		for(size_t i = head; i < line.size(); )
		{
			if(isdigit((unsigned char)line[i]))
			{
				int v = 0;
				while(i < line.size() && isdigit((unsigned char)line[i])) v = v * 10 + (line[i++] - '0');
				nums.push_back(v);
			}
			else i++;
		}
		if(nums.empty() || nums.size() % 2 != 0) continue;
		vector<pair<int, int> > op;
		bool ok = true;
		for(size_t i = 0; i < nums.size(); i += 2)
		{
			if(nums[i] < 0 || nums[i] >= SIZE || nums[i + 1] < 0 || nums[i + 1] >= SIZE) { ok = false; break; }
			op.emplace_back(nums[i], nums[i + 1]);
		}
		if(!ok) continue;
		openings.push_back(move(op));
	}
	cerr << "openings loaded: " << openings.size() << " from " << used << endl;
	return openings;
}

int main(int argc, char** argv)
{
	init_lines();
	init_sq_lines();
	init_cnt_tbl();

	const int games = argc > 1 ? atoi(argv[1]) : 8;
	const int level = argc > 2 ? atoi(argv[2]) : 10;

	const vector<vector<pair<int, int> > > openings = load_openings("unique_opening/unique_openings_4.txt");
	if(openings.empty()) { cerr << "no openings; abort" << endl; return 1; }

	printf("config: games=%d level=%d USE_ENDGAME_R2=%d USE_ENDGAME_CUT=%d EG_SELFCHECK=%d\n",
	       games, level, USE_ENDGAME_R2, USE_ENDGAME_CUT, EG_SELFCHECK);

	double total_sec = 0;
	long long total_nodes = 0;
	int wins[3] = {};
	string move_log;      // 全対局の着手列(OFF ビルド同士の完全一致確認に使う)

	for(int g = 0; g < games; g++)
	{
		AI p1(level, evaluate_pointfir_cont_layer_intersection_rit);
		AI p2(level, evaluate_pointsec_cont_layer_intersection_rit);
		Game game(&p1, &p2, false, openings[g % (int)openings.size()]);
		p1.set_game(&game);
		p2.set_game(&game);

#ifdef BENCH
		const long long n0 = g_node_count;
#endif
		const auto st = chrono::system_clock::now();

		// Game::game() は結果表示を伴うので、ここでは着手ループだけを回す
		enum State ret = State::Continue;
		int turn = 0;
		while(turn < BOARD_SIZE)
		{
			ret = game.move(turn);
			if(ret == State::End) break;
			turn++;
		}

		const double sec = chrono::duration_cast<chrono::milliseconds>(chrono::system_clock::now() - st).count() / 1e3;
#ifdef BENCH
		const long long nodes = g_node_count - n0;
#else
		const long long nodes = 0;
#endif
		enum Color result;
		if(ret == State::End) result = (game.board.validate() == Color::White) ? Color::Black : Color::White;
		else result = Color::Draw;
		wins[result]++;
		total_sec += sec;
		total_nodes += nodes;

		printf("game %2d: moves=%2d result=%-5s %8.3f sec  nodes=%12lld\n",
		       g, (int)game.hand.size(),
		       result == Color::Black ? "Black" : result == Color::White ? "White" : "Draw",
		       sec, nodes);
		fflush(stdout);

		for(auto [x, y] : game.hand) { move_log += (char)('0' + x); move_log += (char)('0' + y); }
		move_log += '\n';
	}

	printf("--------\n");
	printf("total: %.3f sec\n", total_sec);
	printf("nodes: %lld\n", total_nodes);
	printf("result: Black %d / White %d / Draw %d\n", wins[Color::Black], wins[Color::White], wins[Color::Draw]);
#if EG_SELFCHECK
	printf("eg_selfcheck: %lld 件の打ち切りを全読みと照合(不一致は即 abort)\n", g_eg_check_count);
#endif
	printf("== move log ==\n%s", move_log.c_str());
	return 0;
}
