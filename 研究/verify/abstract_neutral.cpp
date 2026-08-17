// 補題 S の機械検証。
//
// 主張(補題 S): 抽象モデル(高い柱が高々1本 = G_T)の任意の到達可能局面で、
//   手番側に「即勝ちマス(自分のラベルが付いた即置可能マス)」が無く、
//   かつ「柱の最上段にある無ラベルの即置可能マス u」(= 消火手の形)が存在するなら、
//   u を打つ手は最善手である(最善値を達成する)。
//
// これが成り立てば、研究\最終盤評価関数_turn57以下の証明.md の戦略 F の手順 2(消火手)が
// 抽象モデルの最善性を一切損なわないことが言える。
//
// ビルド: g++ -O2 -std=c++17 -o abstract_neutral.exe abstract_neutral.cpp
#include <cstdio>
#include <vector>
#include <algorithm>
using namespace std;

static const int MAXE = 12;
enum { L_NONE = 0, L_B = 1, L_W = 2, L_BW = 3 };

static inline int dan(int h, int i) { return 5 - h + i; }
static inline int color_of_turn(int t) { return (t & 1) ? 0 : 1; }

static vector<int> g_h;
static vector<vector<int>> g_lab;
static int g_t0;
static vector<int> g_filled;
static vector<int> g_stride;
static vector<signed char> g_memo;

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
    }
    const int r = (best == -2) ? 0 : best;
    g_memo[key] = (signed char)r;
    return r;
}

// filled[] が表す局面について補題 S を検査する。move_index = 埋まっているマスの総数
static long long g_checked = 0, g_viol = 0;

static void check_state(int move_index)
{
    const int me = color_of_turn(g_t0 + move_index);

    // 即勝ちマス(手番側のラベル)/ 相手の即リーチ(阻止強制)があるか
    bool immediate_win = false, must_block = false;
    for (size_t j = 0; j < g_h.size(); j++)
    {
        const int i = g_filled[j];
        if (i >= g_h[j]) continue;
        const int lab = g_lab[j][i];
        if ((me == 0 && (lab & L_B)) || (me == 1 && (lab & L_W))) immediate_win = true;
        if ((me == 0 && (lab & L_W)) || (me == 1 && (lab & L_B))) must_block  = true;
    }
    if (!immediate_win && !must_block)
    {
        const int best = solve(move_index);
        for (size_t j = 0; j < g_h.size(); j++)
        {
            const int i = g_filled[j];
            if (i >= g_h[j]) continue;
            if (i != g_h[j] - 1) continue;        // 柱の最上段でない
            if (g_lab[j][i] != L_NONE) continue;  // 無ラベルでない
            // u = この柱の最後の 1 マス、無ラベル = 消火手の形
            g_filled[j]++;
            const int v = -solve(move_index + 1);
            g_filled[j]--;
            g_checked++;
            if (v != best)
            {
                g_viol++;
                if (g_viol <= 5)
                {
                    printf("  ### 補題 S 違反: turn=%d 形状=", g_t0 + move_index);
                    for (size_t k = 0; k < g_h.size(); k++)
                        printf("%s%d(埋%d)", k ? "+" : "", g_h[k], g_filled[k]);
                    static const char *nm[4] = {"-","B","W","BW"};
                    printf(" ラベル:");
                    for (size_t k = 0; k < g_h.size(); k++)
                    { printf(" |"); for (int q = 0; q < g_h[k]; q++) printf(" 段%d:%s", dan(g_h[k],q), nm[g_lab[k][q]]); }
                    printf("  最善=%+d 消火手=%+d\n", best, v);
                }
            }
        }
    }
}

// 全「充填状態」を直接列挙する(同じ状態を手順ごとに再訪しないため)
static void check_all_states(int states)
{
    for (int key = 0; key < states; key++)
    {
        int rest = key, mv = 0;
        for (size_t j = 0; j < g_h.size(); j++)
        {
            const int f = rest % (g_h[j] + 1); rest /= (g_h[j] + 1);
            g_filled[j] = f; mv += f;
        }
        check_state(mv);
    }
}

static void gen_shapes(int rest, int maxpart, vector<int> &cur, vector<vector<int>> &out)
{
    if (rest == 0) { out.push_back(cur); return; }
    for (int p = min(rest, maxpart); p >= 1; p--)
    { cur.push_back(p); gen_shapes(rest - p, p, cur, out); cur.pop_back(); }
}

int main()
{
    printf("補題 S の検証(抽象モデル・G_T・E<=%d の全ラベル割当 × 全到達局面)\n\n", MAXE);
    for (int E = 1; E <= MAXE; E++)
    {
        const int turn = 65 - E;
        vector<vector<int>> shapes; vector<int> cur;
        gen_shapes(E, 4, cur, shapes);
        const long long c0 = g_checked, v0 = g_viol;
        for (const vector<int> &h : shapes)
        {
            int tall = 0; for (int x : h) if (x >= 3) tall++;
            if (tall > 1) continue;
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
                check_all_states(states);
            }
        }
        printf("E=%2d (turn=%2d): 消火手の検査 %10lld 件 / 違反 %lld\n",
               E, turn, g_checked - c0, g_viol - v0);
    }
    printf("\n合計 %lld 件検査 / 違反 %lld → 補題 S は E<=%d で %s\n",
           g_checked, g_viol, MAXE, g_viol == 0 ? "成立" : "不成立");
    return 0;
}
