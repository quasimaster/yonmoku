// 抽象モデル(脅威創出なし)の完全列挙 — 「高い柱が高々1本」に限定して E を 12 まで伸ばす。
//
// abstract_endgame.cpp は E <= 10 までの全形状を尽くすが、
// 研究\最終盤評価関数_turn57以下の証明.md の還元定理(定理 R)は
//   「代表形 = K(高さ3or4の柱, 0/1本) + 中立マス N ∈ {0,1} + 各種スタック 0/1 本ずつ」
// まで落ちるので、その全代表形を含む E <= 12 を実際に確認すれば構造定理が全 E で閉じる。
// (代表形の最大 E は K=4 + N=1 + 2*3 = 11)
//
// ビルド: g++ -O2 -std=c++17 -o abstract_tall1.exe abstract_tall1.cpp
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>
using namespace std;

static const int MAXE = 12;

enum { L_NONE = 0, L_B = 1, L_W = 2, L_BW = 3 };

static inline int dan(int h, int i) { return 5 - h + i; }          // 補題2
static inline int color_of_turn(int t) { return (t & 1) ? 0 : 1; } // 0=黒 1=白

static vector<int>  g_h;
static vector<vector<int>> g_lab;
static int g_t0;
static vector<int> g_filled;
static vector<int> g_stride;
static vector<signed char> g_memo;   // -2 = 未計算

static int solve(int move_index)
{
    int key = 0;
    for (size_t j = 0; j < g_h.size(); j++) key += g_filled[j] * g_stride[j];
    if (g_memo[key] != -2) return g_memo[key];

    const int me = color_of_turn(g_t0 + move_index);
    int best = -2;
    for (size_t j = 0; j < g_h.size(); j++)
    {
        const int i = g_filled[j];
        if (i >= g_h[j]) continue;
        const int lab = g_lab[j][i];
        int v;
        if ((me == 0 && (lab & L_B)) || (me == 1 && (lab & L_W))) v = +1;
        else { g_filled[j]++; v = -solve(move_index + 1); g_filled[j]--; }
        if (v > best) best = v;
        if (best == 1) break;
    }
    const int r = (best == -2) ? 0 : best;
    g_memo[key] = (signed char)r;
    return r;
}

static int ruleR2(void)
{
    for (int m = 1; m <= 4; m++)
        for (size_t j = 0; j < g_h.size(); j++)
            for (int i = 1; i < g_h[j]; i++)
            {
                if (dan(g_h[j], i) != m) continue;
                const int lab = g_lab[j][i];
                if ( (m & 1) && (lab & L_B)) return color_of_turn(g_t0) == 0 ? +1 : -1;
                if (!(m & 1) && (lab & L_W)) return color_of_turn(g_t0) == 1 ? +1 : -1;
            }
    return 0;
}

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

int main()
{
    printf("抽象モデル完全列挙(高い柱 h>=3 が高々1本 = G_T のみ)\n\n");
    long long gn = 0, gmiss = 0, gbad = 0;

    for (int E = 1; E <= MAXE; E++)
    {
        const int turn = 65 - E;
        vector<vector<int>> shapes; vector<int> cur;
        gen_shapes(E, 4, cur, shapes);

        long long n = 0, miss = 0, bad = 0, nshape = 0;
        for (const vector<int> &h : shapes)
        {
            int tall = 0; for (int x : h) if (x >= 3) tall++;
            if (tall > 1) continue;                       // G_T 違反は対象外
            nshape++;

            g_h = h; g_t0 = turn;
            g_lab.assign(h.size(), {});
            for (size_t j = 0; j < h.size(); j++) g_lab[j].assign(h[j], L_NONE);

            g_stride.assign(h.size(), 1);
            int states = 1;
            for (size_t j = 0; j < h.size(); j++) { g_stride[j] = states; states *= (h[j] + 1); }

            vector<pair<int,int>> buried;
            for (size_t j = 0; j < h.size(); j++) for (int i = 1; i < h[j]; i++) buried.push_back({(int)j, i});

            const long long total = 1LL << (2 * buried.size());
            for (long long mask = 0; mask < total; mask++)
            {
                for (size_t k = 0; k < buried.size(); k++)
                    g_lab[buried[k].first][buried[k].second] = (int)((mask >> (2 * k)) & 3);

                g_filled.assign(h.size(), 0);
                g_memo.assign(states, -2);
                const int exact = solve(0), v2 = ruleR2();
                n++;
                if (v2 != exact) { if (v2 == 0) miss++; else bad++;
                    if (miss + bad <= 3)
                    {
                        printf("  ### 不一致 E=%d turn=%d 形状=", E, turn);
                        for (size_t j = 0; j < h.size(); j++) printf("%s%d", j ? "+" : "", h[j]);
                        static const char *nm[4] = {"-","B","W","BW"};
                        printf("  ラベル:");
                        for (size_t j = 0; j < h.size(); j++)
                        { printf(" |"); for (int i = 0; i < h[j]; i++) printf(" 段%d:%s", dan(h[j],i), nm[g_lab[j][i]]); }
                        printf("  厳密=%+d R2=%+d\n", exact, v2);
                    }
                }
            }
        }
        printf("E=%2d (turn=%2d) 形状 %3lld 種 / パターン %10lld : 取りこぼし %lld 誤断定 %lld%s\n",
               E, turn, nshape, n, miss, bad, (miss==0&&bad==0) ? "  ← 完全一致" : "");
        gn += n; gmiss += miss; gbad += bad;
    }
    printf("\n合計 %lld パターン : 取りこぼし %lld / 誤断定 %lld → 構造定理は E<=%d で %s\n",
           gn, gmiss, gbad, MAXE, (gmiss==0&&gbad==0) ? "成立" : "不成立");
    return 0;
}
