// 規則 R3(解放数によるツークツワンク規則)の検証。
//
// 仮説(定理 N):抽象モデルで「各柱のラベル付きマスが高々 1 個」のとき、局面の値は
//   ・中立マスの総数 N の偶奇と手番(= どちらが「詰まる側」P か)
//   ・各色の脅威の「解放数 ρ = 4 - λ」の偶奇の本数(λ = 脅威の段)
//   ・双方毒(BW)脅威の有無
// だけで決まる。ρ が奇数 ⟺ λ = 3。すなわち「段3 の脅威だけがツークツワンクの手番を押し返せる」。
//
// 各柱 j(高さ h、ラベルが下から i 番目 = 段 λ = 5-h+i)について
//   ゲート  = 下から i-1 番目
//   中立マス(ゲートより下)= i-1 個
//   解放マス(脅威より上)  = h-1-i 個 = 4-λ
// ラベルが無い柱は h 個ぜんぶ中立。
//
// ビルド: g++ -O2 -std=c++17 -o abstract_r3.exe abstract_r3.cpp
#include <cstdio>
#include <vector>
#include <algorithm>
using namespace std;

static const int MAXE = 13;
enum { L_NONE = 0, L_B = 1, L_W = 2, L_BW = 3 };

static inline int dan(int h, int i) { return 5 - h + i; }
static inline int color_of_turn(int t) { return (t & 1) ? 0 : 1; }   // 0=黒 1=白

static vector<int> g_h;
static vector<vector<int>> g_lab;
static int g_t0;
static vector<int> g_filled, g_stride;
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
        if (best == 1) break;
    }
    const int r = (best == -2) ? 0 : best;
    g_memo[key] = (signed char)r;
    return r;
}

// 規則 R2(低段優先の段パリティ)。手番視点
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

// ---- 縮約ゲームの求解 ----------------------------------------------------
// 状態: 詰まる側 stuck、各色の 奇数解放スタック数 o[2] / 偶数解放スタック数 e[2]、双方毒 gamma
// 返り値: 絶対視点の勝者 (0=黒勝ち, 1=白勝ち, 2=引き分け)
static int reduce_solve(int stuck, int o[2], int e[2], int gamma)
{
    const int q = 1 - stuck;
    if (o[stuck] == 0 && e[stuck] == 0)
        return (o[q] || e[q] || gamma) ? q : 2;          // 燃やす手が無い → 毒があれば負け

    int best = -1;   // stuck から見て 良い順に: 勝ち(=stuck) > 引き分け(2) > 負け(=q)
    auto better = [&](int a, int b) {
        auto rank = [&](int r) { return r == stuck ? 2 : (r == 2 ? 1 : 0); };
        return rank(a) >= rank(b) ? a : b;
    };
    if (o[stuck]) { o[stuck]--; const int r = reduce_solve(q,     o, e, gamma); o[stuck]++;
                    best = (best < 0) ? r : better(best, r); }
    if (e[stuck]) { e[stuck]--; const int r = reduce_solve(stuck, o, e, gamma); e[stuck]++;
                    best = (best < 0) ? r : better(best, r); }
    return best;
}

// 規則 R3。手番視点(+1 = 手番の勝ち)。ラベルが 2 個以上ある柱があれば -9 を返す(対象外)
static int ruleR3(void)
{
    int N = 0, o[2] = {0, 0}, e[2] = {0, 0}, gamma = 0;
    for (size_t j = 0; j < g_h.size(); j++)
    {
        int idx = -1, cnt = 0;
        for (int i = 1; i < g_h[j]; i++) if (g_lab[j][i] != L_NONE) { idx = i; cnt++; }
        if (cnt >= 2) return -9;
        if (cnt == 0) { N += g_h[j]; continue; }
        N += idx - 1;                                   // ゲートより下の中立マス
        const int lam = dan(g_h[j], idx);               // 脅威の段
        const int lab = g_lab[j][idx];
        if (lab == L_BW) gamma++;
        else
        {
            const int col = (lab == L_B) ? 0 : 1;
            if ((4 - lam) & 1) o[col]++; else e[col]++; // 解放数 4-λ の偶奇
        }
    }
    const int mover = color_of_turn(g_t0);
    const int stuck = (N % 2 == 0) ? mover : (1 - mover);
    const int win = reduce_solve(stuck, o, e, gamma);
    if (win == 2) return 0;
    return (win == mover) ? +1 : -1;
}

static void gen_shapes(int rest, int maxpart, vector<int> &cur, vector<vector<int>> &out)
{
    if (rest == 0) { out.push_back(cur); return; }
    for (int p = min(rest, maxpart); p >= 1; p--)
    { cur.push_back(p); gen_shapes(rest - p, p, cur, out); cur.pop_back(); }
}

int main()
{
    printf("R3(解放数によるツークツワンク規則)の検証 — 各柱のラベルは高々 1 個\n\n");
    long long gn = 0, g2bad = 0, g2miss = 0, g3bad = 0, g3miss = 0;
    long long byTallN[6] = {0}, byTall2[6] = {0}, byTall3[6] = {0};
    int shown = 0;

    for (int E = 1; E <= MAXE; E++)
    {
        const int turn = 65 - E;
        vector<vector<int>> shapes; vector<int> cur;
        gen_shapes(E, 4, cur, shapes);
        long long n = 0, b2 = 0, m2 = 0, b3 = 0, m3 = 0;

        for (const vector<int> &h : shapes)
        {
            g_h = h; g_t0 = turn;
            g_lab.assign(h.size(), {});
            for (size_t j = 0; j < h.size(); j++) g_lab[j].assign(h[j], L_NONE);
            g_stride.assign(h.size(), 1);
            int states = 1;
            for (size_t j = 0; j < h.size(); j++) { g_stride[j] = states; states *= (h[j] + 1); }

            // 各柱の選択肢: ラベル無し / (位置 i ∈ 1..h-1) × (B, W, BW)
            vector<int> opt(h.size());
            long long total = 1;
            for (size_t j = 0; j < h.size(); j++) { opt[j] = 1 + 3 * (h[j] - 1); total *= opt[j]; }

            int tall = 0; for (int x : h) if (x >= 3) tall++;
            const int tk = tall < 5 ? tall : 5;

            for (long long mask = 0; mask < total; mask++)
            {
                long long r = mask;
                for (size_t j = 0; j < h.size(); j++)
                {
                    const int c = (int)(r % opt[j]); r /= opt[j];
                    for (int i = 0; i < h[j]; i++) g_lab[j][i] = L_NONE;
                    if (c > 0) g_lab[j][1 + (c - 1) / 3] = 1 + (c - 1) % 3;
                }
                g_filled.assign(h.size(), 0);
                g_memo.assign(states, -2);
                const int exact = solve(0), v2 = ruleR2(), v3 = ruleR3();
                n++; gn++; byTallN[tk]++;
                if (v2 != exact) { if (v2 == 0) m2++; else b2++; byTall2[tk]++; }
                if (v3 != exact) { if (v3 == 0) m3++; else b3++; byTall3[tk]++;
                    if (++shown <= 4)
                    {
                        printf("  ### R3 不一致 E=%d turn=%d 形状=", E, turn);
                        for (size_t j = 0; j < h.size(); j++) printf("%s%d", j ? "+" : "", h[j]);
                        static const char *nm[4] = {"-","B","W","BW"};
                        for (size_t j = 0; j < h.size(); j++)
                        { printf(" |"); for (int i = 0; i < h[j]; i++) printf(" 段%d:%s", dan(h[j],i), nm[g_lab[j][i]]); }
                        printf("  厳密=%+d R2=%+d R3=%+d\n", exact, v2, v3);
                    }
                }
            }
        }
        printf("E=%2d (turn=%2d) : %9lld パターン | R2 取%6lld 誤%6lld | R3 取%6lld 誤%6lld%s\n",
               E, turn, n, m2, b2, m3, b3, (m3 == 0 && b3 == 0) ? "  ← R3 完全一致" : "");
        g2miss += m2; g2bad += b2; g3miss += m3; g3bad += b3;
    }
    printf("\n合計 %lld パターン | R2: 取りこぼし %lld 誤断定 %lld | R3: 取りこぼし %lld 誤断定 %lld\n",
           gn, g2miss, g2bad, g3miss, g3bad);
    printf("\n[高い柱(h>=3)の本数による層別]\n");
    for (int k = 0; k <= 5; k++) if (byTallN[k])
        printf("  tall=%d : %10lld パターン  R2 不一致 %8lld (%.2f%%)  R3 不一致 %8lld\n",
               k, byTallN[k], byTall2[k], 100.0 * byTall2[k] / byTallN[k], byTall3[k]);
    return 0;
}
