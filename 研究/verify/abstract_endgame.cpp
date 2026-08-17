// 最終盤の「脅威創出が起きない世界」における完全列挙。
//
// 前提(研究結果 §3 の定理の仮定):
//   - 制約(C): 即座に置けるマスには双方リーチが無い
//   - 脅威創出不可能: 以後どちらも新しいリーチを作れない
//     → 補題3(リーチ不滅性)と併せて、各空きマスの「誰のリーチか」というラベルは不変。
//
// このときゲームは次の抽象モデルと完全に同型になる:
//   - 盤面 = 柱(スタック)の集合。柱 j は高さ h_j の空きマスを持ち、下から順にしか置けない。
//   - 柱 j の下から i 番目のマスの段は 5 - h_j + i (補題2)。
//   - 各マスにラベル {なし, 黒, 白, 両方} が付く。制約(C)より各柱の最下段(i=0)は必ず「なし」。
//   - 手番はマスを 1 つ選んで埋める。自分のラベルが付いたマスを埋めたらその場で勝ち。
//   - 全マスが埋まったら引き分け。
//
// 本プログラムは E = 1..MAXE について「全ての柱形状 × 全てのラベル割当」を列挙し、
// 厳密解と規則 R1/R2 を突き合わせる。全割当を尽くすので、実際の盤面で実現可能な配置は
// 必ずこの中に含まれる(上位集合)。したがって「全件一致」なら実盤面でも厳密である。
//
// ビルド: g++ -O2 -std=c++17 -o abstract_endgame.exe abstract_endgame.cpp
#include <cstdio>
#include <cstring>
#include <vector>
#include <array>
#include <algorithm>
using namespace std;

static const int MAXE = 10;

// 仮説: R2 が破れるのは「高さ3以上の柱が2本以上」あるときに限る。
// (高さ3以上の柱だけが段3以下に埋没マスを持つ = 互いに潰し合う脅威を置ける)
static long long hyp_tall_le1_n = 0, hyp_tall_le1_bad = 0, hyp_tall_le1_miss = 0;
static long long hyp_tall_ge2_n = 0, hyp_tall_ge2_bad = 0, hyp_tall_ge2_miss = 0;

enum { L_NONE = 0, L_B = 1, L_W = 2, L_BW = 3 };

struct Shape
{
	vector<int> h;                 // 各柱の空きマス数(降順)
	vector<vector<int>> label;     // label[j][i] : 柱 j の下から i 番目のラベル
	int E;
	int t0;                        // 最初の手の turn 番号 = 65 - E
};

// 段: 柱の高さ h、下から i 番目 → 5 - h + i
static inline int dan(int h, int i) { return 5 - h + i; }

// turn が奇数なら黒。黒 = 0, 白 = 1 で表す
static inline int color_of_turn(int turn) { return (turn & 1) ? 0 : 1; }

static Shape *g_s;
static vector<int> g_filled;

// 厳密解: 手番視点で +1 / 0 / -1
static int solve_abs(int move_index)
{
	const int turn = g_s->t0 + move_index;
	const int me = color_of_turn(turn);
	int best = -2;
	for (size_t j = 0; j < g_s->h.size(); j++)
	{
		const int i = g_filled[j];
		if (i >= g_s->h[j]) continue;
		const int lab = g_s->label[j][i];
		int v;
		if ((me == 0 && (lab & L_B)) || (me == 1 && (lab & L_W))) v = +1;   // 自分のリーチを埋めた → 勝ち
		else
		{
			g_filled[j]++;
			v = -solve_abs(move_index + 1);
			g_filled[j]--;
		}
		if (v > best) best = v;
		if (best == 1) break;
	}
	return best == -2 ? 0 : best;   // 置けるマスが無い = 引き分け
}

// 規則 R2 (段パリティ + 低段優先)。手番視点の値を返す
static int ruleR2_abs(const Shape &s)
{
	for (int m = 1; m <= 4; m++)
	{
		for (size_t j = 0; j < s.h.size(); j++)
			for (int i = 1; i < s.h[j]; i++)     // i=0 は制約(C)より必ず「なし」
			{
				if (dan(s.h[j], i) != m) continue;
				const int lab = s.label[j][i];
				if ((m & 1) && (lab & L_B)) return color_of_turn(s.t0) == 0 ? +1 : -1;
				if (!(m & 1) && (lab & L_W)) return color_of_turn(s.t0) == 1 ? +1 : -1;
			}
	}
	return 0;
}

// 規則 R1 (段パリティ + 黒優先 = 低段優先を入れない版)
static int ruleR1_abs(const Shape &s)
{
	bool bw = false, ww = false;
	for (size_t j = 0; j < s.h.size(); j++)
		for (int i = 1; i < s.h[j]; i++)
		{
			const int m = dan(s.h[j], i), lab = s.label[j][i];
			if ((m & 1) && (lab & L_B)) bw = true;
			if (!(m & 1) && (lab & L_W)) ww = true;
		}
	int v = bw ? +1 : (ww ? -1 : 0);
	return color_of_turn(s.t0) == 0 ? v : -v;
}

static void shape_str(const Shape &s, char *buf)
{
	int p = 0;
	for (size_t j = 0; j < s.h.size(); j++) p += sprintf(buf + p, "%s%d", j ? "+" : "", s.h[j]);
}

static void label_str(const Shape &s, char *buf)
{
	static const char *nm[4] = {"-", "黒", "白", "両"};
	int p = 0;
	for (size_t j = 0; j < s.h.size(); j++)
	{
		if (j) p += sprintf(buf + p, " / ");
		for (int i = 0; i < s.h[j]; i++)
			p += sprintf(buf + p, "%s段%d:%s", i ? " " : "", dan(s.h[j], i), nm[s.label[j][i]]);
	}
}

// 柱形状(1..4 の部分を持つ E の分割、降順)を列挙
static void gen_shapes(int rest, int maxpart, vector<int> &cur, vector<vector<int>> &out)
{
	if (rest == 0) { out.push_back(cur); return; }
	for (int p = min(rest, maxpart); p >= 1; p--)
	{
		cur.push_back(p);
		gen_shapes(rest - p, p, cur, out);
		cur.pop_back();
	}
}

struct Res
{
	long long n = 0, ok1 = 0, ok2 = 0, bad1 = 0, bad2 = 0, miss1 = 0, miss2 = 0;
	long long win = 0, draw = 0, lose = 0;
};

int main()
{
	printf("脅威創出が起きない抽象モデルでの完全列挙\n");
	printf("(全柱形状 × 全ラベル割当。制約(C)より各柱の最下段はラベル無しに固定)\n\n");

	bool first_fail_reported = false;

	for (int E = 1; E <= MAXE; E++)
	{
		const int turn = 65 - E;
		vector<vector<int>> shapes;
		vector<int> cur;
		gen_shapes(E, 4, cur, shapes);

		Res tot;
		printf("======== E = %d (turn = %d, 手番 = %s) ========\n",
		       E, turn, color_of_turn(turn) == 0 ? "黒" : "白");
		printf("%-12s %10s %8s %8s %8s | %-22s | %-22s\n",
		       "柱形状", "全パターン", "勝ち", "分け", "負け", "R1(黒優先)", "R2(低段優先)");

		for (const vector<int> &h : shapes)
		{
			Shape s;
			s.h = h; s.E = E; s.t0 = turn;
			s.label.assign(h.size(), {});
			for (size_t j = 0; j < h.size(); j++) s.label[j].assign(h[j], L_NONE);

			// 埋没マス(各柱の i>=1)の一覧
			vector<pair<int,int>> buried;
			for (size_t j = 0; j < h.size(); j++) for (int i = 1; i < h[j]; i++) buried.push_back({(int)j, i});

			Res r;
			const long long total = 1LL << (2 * buried.size());
			for (long long mask = 0; mask < total; mask++)
			{
				for (size_t k = 0; k < buried.size(); k++)
					s.label[buried[k].first][buried[k].second] = (int)((mask >> (2 * k)) & 3);

				g_s = &s;
				g_filled.assign(h.size(), 0);
				const int exact = solve_abs(0);
				const int v1 = ruleR1_abs(s), v2 = ruleR2_abs(s);

				int tall = 0;
				for (int hh : h) if (hh >= 3) tall++;
				if (tall <= 1) { hyp_tall_le1_n++; if (v2 != exact) { if (v2 == 0) hyp_tall_le1_miss++; else hyp_tall_le1_bad++; } }
				else           { hyp_tall_ge2_n++; if (v2 != exact) { if (v2 == 0) hyp_tall_ge2_miss++; else hyp_tall_ge2_bad++; } }

				r.n++;
				if (exact > 0) r.win++; else if (exact < 0) r.lose++; else r.draw++;
				if (v1 == exact) r.ok1++; else if (v1 == 0) r.miss1++; else r.bad1++;
				if (v2 == exact) r.ok2++; else if (v2 == 0) r.miss2++; else r.bad2++;

				if (v2 != exact && !first_fail_reported)
				{
					char sb[64], lb[512];
					shape_str(s, sb); label_str(s, lb);
					printf("\n  ### R2 が初めて外れる最小反例 ###\n");
					printf("  E=%d turn=%d 形状=%s\n  ラベル: %s\n", E, turn, sb, lb);
					printf("  厳密解(手番視点)=%+d  R2=%+d\n\n", exact, v2);
					first_fail_reported = true;
				}
			}

			char sb[64];
			shape_str(s, sb);
			printf("%-12s %10lld %8lld %8lld %8lld | ok%7lld 取%5lld 誤%5lld | ok%7lld 取%5lld 誤%5lld\n",
			       sb, r.n, r.win, r.draw, r.lose,
			       r.ok1, r.miss1, r.bad1, r.ok2, r.miss2, r.bad2);

			tot.n += r.n; tot.win += r.win; tot.draw += r.draw; tot.lose += r.lose;
			tot.ok1 += r.ok1; tot.miss1 += r.miss1; tot.bad1 += r.bad1;
			tot.ok2 += r.ok2; tot.miss2 += r.miss2; tot.bad2 += r.bad2;
		}
		printf("%-12s %10lld %8lld %8lld %8lld | ok%7lld 取%5lld 誤%5lld | ok%7lld 取%5lld 誤%5lld\n",
		       "合計", tot.n, tot.win, tot.draw, tot.lose,
		       tot.ok1, tot.miss1, tot.bad1, tot.ok2, tot.miss2, tot.bad2);
		printf("  → R2 一致率 %.4f%%%s\n\n", 100.0 * tot.ok2 / tot.n,
		       tot.ok2 == tot.n ? "  (完全一致 = この E では R2 は厳密)" : "");
	}

	printf("======== 仮説の検証 (E=1..%d の全パターン) ========\n", MAXE);
	printf("高さ3以上の柱が1本以下 : %10lld 件中  取りこぼし %lld / 誤断定 %lld\n",
	       hyp_tall_le1_n, hyp_tall_le1_miss, hyp_tall_le1_bad);
	printf("高さ3以上の柱が2本以上 : %10lld 件中  取りこぼし %lld / 誤断定 %lld\n",
	       hyp_tall_ge2_n, hyp_tall_ge2_miss, hyp_tall_ge2_bad);
	printf("→ 仮説「R2 が破れるのは高さ3以上の柱が2本以上あるときに限る」は %s\n",
	       (hyp_tall_le1_miss == 0 && hyp_tall_le1_bad == 0) ? "成立" : "不成立");
	printf("  空きマス E <= 5 では高さ3以上の柱は高々1本しか作れない → turn >= 60 で R2 は厳密\n");
	return 0;
}
