#pragma once

// bench_core.cpp / bench_core2.cpp の共通本体。
// include する側で AI / Weights / EvalFnT / init_tables() を定義しておくこと。

// 定跡(重複なし初手列)。bench_endgame_selfplay.cpp の load_openings と同一。
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
	init_tables();

	const int games  = argc > 1 ? atoi(argv[1]) : 8;
	const int level  = argc > 2 ? atoi(argv[2]) : 10;
	const int offset = argc > 4 ? atoi(argv[4]) : 0;

	// 重みの決定。第 3 引数が "-" 以外ならファイルから読む(失敗したら即終了。既定値へは戻さない)
	static Weights loaded;
	const Weights* W = &Weights::builtin();
	if(argc > 3 && string(argv[3]) != "-")
	{
		string err;
		if(!loaded.load(argv[3], &err)) { cerr << "weights error: " << err << endl; return 1; }
		W = &loaded;
	}
	cerr << "weights: " << W->base.name << (W == &loaded ? string(" (from ") + argv[3] + ")" : string(" (builtin)"))
	     << (W->has_core() ? " core: on" : " core: all 0") << endl;

	const vector<vector<pair<int, int> > > openings = load_openings("unique_opening/unique_openings_4.txt");
	if(openings.empty()) { cerr << "no openings; abort" << endl; return 1; }

	printf("config: games=%d level=%d offset=%d USE_ENDGAME_R2=%d USE_ENDGAME_CUT=%d\n",
	       games, level, offset, USE_ENDGAME_R2, USE_ENDGAME_CUT);

	double total_sec = 0;
	long long total_nodes = 0;
	int wins[3] = {};
	string move_log;      // 全対局の着手列(改修前後の完全一致確認に使う)
	string score_log;     // 全対局の root 評価値列(同上)

	for(int g = 0; g < games; g++)
	{
		AI p1(level, EvalFnT{W, false});
		AI p2(level, EvalFnT{W, true });
		Game game(&p1, &p2, false, openings[(g + offset) % (int)openings.size()]);
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
		       g + offset, (int)game.hand.size(),
		       result == Color::Black ? "Black" : result == Color::White ? "White" : "Draw",
		       sec, nodes);
		fflush(stdout);

		for(auto [x, y] : game.hand) { move_log += (char)('0' + x); move_log += (char)('0' + y); }
		move_log += '\n';
		{
			char buf[32];
			snprintf(buf, sizeof(buf), "g%d fir:", g + offset); score_log += buf;
			for(int i = 1; i < 33; i++) { snprintf(buf, sizeof(buf), " %d", game.evaluatesfir_tmp[i]); score_log += buf; }
			snprintf(buf, sizeof(buf), "\ng%d sec:", g + offset); score_log += buf;
			for(int i = 1; i < 33; i++) { snprintf(buf, sizeof(buf), " %d", game.evaluatessec_tmp[i]); score_log += buf; }
			score_log += '\n';
		}
	}

	printf("--------\n");
	printf("total: %.3f sec\n", total_sec);
	printf("nodes: %lld\n", total_nodes);
	printf("result: Black %d / White %d / Draw %d\n", wins[Color::Black], wins[Color::White], wins[Color::Draw]);
	printf("== move log ==\n%s", move_log.c_str());
	printf("== score log (root value per AI turn; INF = not searched) ==\n%s", score_log.c_str());
	return 0;
}
