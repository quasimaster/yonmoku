// 規則 R3 の「run(1 本の柱に脅威が 2 個以上)」への拡張版。
//
// 柱を「ブロック」の列に分解する。1 ブロック = [ゲートより下の中立マス nu 個] + [ゲート 1] + [連続ラベル run r 個]。
// 補題Q より、ゲートを踏んだときの結果は踏む側の色で決まる:
//   A = owner(ゲートの段) が踏む → run 中の最初の「有効脅威」の持ち主が勝つ(無ければ素通り)
//   B = opp(A)            が踏む → run 中の最初の「無効脅威」の持ち主が勝つ(無ければ素通り)
// 素通り(= burn)したときは 1+r マスを消費し、その上の中立マス nu' がプールに解放される。
// 詰まる側 s は  s XOR (r が偶数) XOR (nu' が奇数)  に移る。
//
// ビルド: g++ -O2 -std=c++17 -o abstract_r3run.exe abstract_r3run.cpp
#include <cstdio>
#include <vector>
#include <algorithm>
#include <map>
using namespace std;

static int MAXE = 11;
enum { L_NONE = 0, L_B = 1, L_W = 2, L_BW = 3 };
enum { WIN_B = 0, WIN_W = 1, PASS = 2 };

static inline int dan(int h, int i) { return 5 - h + i; }
static inline int owner_of(int lev) { return (lev & 1) ? 0 : 1; }   // 段が奇数→黒(0)、偶数→白(1)
static inline int color_of_turn(int t) { return (t & 1) ? 0 : 1; }

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

// ---- ブロック分解 --------------------------------------------------------
struct Block { int gateLev, r, nuNext, outA, outB; };
static vector<vector<Block>> g_blk;        // 柱ごとのブロック列
static vector<int> g_nu0;                  // 柱ごとの「最初のゲート手前の中立マス数」
static int g_Nfree0;                       // ブロックを持たない柱の中立マス総数

static void decompose(void)
{
    g_blk.assign(g_h.size(), {});
    g_nu0.assign(g_h.size(), 0);
    g_Nfree0 = 0;
    for (size_t j = 0; j < g_h.size(); j++)
    {
        const int h = g_h[j];
        int i = 0;
        vector<Block> bl;
        vector<int> nuList;
        while (i < h)
        {
            int k = -1;
            for (int t = i; t < h; t++) if (g_lab[j][t] != L_NONE) { k = t; break; }
            if (k < 0) { nuList.push_back(h - i); break; }        // 以後ぜんぶ中立
            nuList.push_back(k - 1 - i);                          // ゲートより下の中立マス
            int r = 0;
            while (k + r < h && g_lab[j][k + r] != L_NONE) r++;
            Block b;
            b.gateLev = dan(h, k - 1);
            b.r = r;
            // A = owner(gateLev) が踏む → 最初の「有効脅威」
            b.outA = PASS;
            for (int t = k; t < k + r; t++)
            {
                const int lev = dan(h, t), ow = owner_of(lev);
                if (g_lab[j][t] & (ow == 0 ? L_B : L_W)) { b.outA = ow; break; }
            }
            // B = opp(A) が踏む → 最初の「無効脅威」
            b.outB = PASS;
            for (int t = k; t < k + r; t++)
            {
                const int lev = dan(h, t), ow = owner_of(lev), op = 1 - ow;
                if (g_lab[j][t] & (op == 0 ? L_B : L_W)) { b.outB = op; break; }
            }
            bl.push_back(b);
            i = k + r;
        }
        if (nuList.empty()) nuList.push_back(0);
        // nuList[0] は最初のゲートより下、nuList[t] は t 番目のブロックの上(= t+1 番目のゲートより下)
        if (bl.empty()) g_Nfree0 += nuList[0];      // ブロック無し = ぜんぶ自由マス
        else            g_nu0[j]  = nuList[0];      // ゲート手前(順序制約あり)
        for (size_t t = 0; t < bl.size(); t++)
            bl[t].nuNext = (t + 1 < nuList.size()) ? nuList[t + 1] : 0;
        g_blk[j] = bl;
    }
}

// ---- 縮約ゲーム ----------------------------------------------------------
// 中立マスは「どの柱にも属さない自由マス Nfree」と「ブロック持ちの柱のゲート手前のマス c_j」に分かれる。
// c_j は「その柱のゲートを踏めるようにするために埋めねばならない中立マス」で、重力の順序制約を持つ。
// 状態: 手番 mover / Nfree / 各ブロック柱の (bi_j, c_j)
static vector<vector<Block>> g_bcol;      // ブロックを持つ柱だけ
static vector<int> g_bnu0;                // その柱の最初のゲート手前の中立マス数
static int g_Nfree;

static int rec(int mover, int Nfree, vector<int> &bi, vector<int> &c, map<vector<int>,int> &memo)
{
    vector<int> key;
    key.push_back(mover); key.push_back(Nfree);
    for (size_t j = 0; j < bi.size(); j++) { key.push_back(bi[j]); key.push_back(c[j]); }
    auto it = memo.find(key);
    if (it != memo.end()) return it->second;

    const int q = 1 - mover;
    int best = -1;
    auto rank = [&](int r) { return r == mover ? 2 : (r == 2 ? 1 : 0); };
    auto upd  = [&](int r) { if (best < 0 || rank(r) > rank(best)) best = r; };

    if (Nfree > 0) upd(rec(q, Nfree - 1, bi, c, memo));

    for (size_t j = 0; j < bi.size(); j++)
    {
        if (bi[j] >= (int)g_bcol[j].size()) { if (c[j] > 0) { c[j]--; upd(rec(q, Nfree, bi, c, memo)); c[j]++; } continue; }
        if (c[j] > 0) { c[j]--; upd(rec(q, Nfree, bi, c, memo)); c[j]++; continue; }
        const Block &b = g_bcol[j][bi[j]];
        const int A = owner_of(b.gateLev);
        const int out = (mover == A) ? b.outA : b.outB;
        if (out == mover) { best = mover; break; }             // 踏んで勝てる
        if (out == q) { upd(q); continue; }                    // 毒
        const int nm = (b.r % 2 == 1) ? mover : q;             // 素通り: 1+r 手
        bi[j]++; const int save = c[j]; c[j] = b.nuNext;
        upd(rec(nm, Nfree, bi, c, memo));
        c[j] = save; bi[j]--;
    }
    if (best < 0) best = 2;                                    // 打つ手が無い = 盤が埋まった
    memo[key] = best;
    return best;
}

static int ruleR3(void)
{
    decompose();
    g_bcol.clear(); g_bnu0.clear(); g_Nfree = g_Nfree0;
    for (size_t j = 0; j < g_blk.size(); j++)
    {
        if (g_blk[j].empty()) continue;
        g_bcol.push_back(g_blk[j]);
        g_bnu0.push_back(g_nu0[j]);
    }
    const int mover = color_of_turn(g_t0);
    vector<int> bi(g_bcol.size(), 0), c = g_bnu0;
    map<vector<int>,int> memo;
    const int win = rec(mover, g_Nfree % 2, bi, c, memo);   // 自由マスは偶奇だけ
    if (win == 2) return 0;
    return (win == mover) ? +1 : -1;
}

static void gen_shapes(int rest, int maxpart, vector<int> &cur, vector<vector<int>> &out)
{
    if (rest == 0) { out.push_back(cur); return; }
    for (int p = min(rest, maxpart); p >= 1; p--)
    { cur.push_back(p); gen_shapes(rest - p, p, cur, out); cur.pop_back(); }
}

int main(int argc, char **argv)
{
    if (argc > 1) MAXE = atoi(argv[1]);
    printf("R3(run 拡張版)の検証 — 全ラベル割当・柱の高さ無制限\n\n");
    long long gn = 0, g2 = 0, g3m = 0, g3b = 0;
    long long tN[6] = {0}, t2[6] = {0}, t3[6] = {0};
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
            vector<pair<int,int>> buried;
            for (size_t j = 0; j < h.size(); j++) for (int i = 1; i < h[j]; i++) buried.push_back({(int)j, i});
            const long long total = 1LL << (2 * buried.size());
            int tall = 0; for (int x : h) if (x >= 3) tall++;
            const int tk = tall < 5 ? tall : 5;

            for (long long mask = 0; mask < total; mask++)
            {
                for (size_t k = 0; k < buried.size(); k++)
                    g_lab[buried[k].first][buried[k].second] = (int)((mask >> (2 * k)) & 3);
                g_filled.assign(h.size(), 0);
                g_memo.assign(states, -2);
                const int exact = solve(0), v2 = ruleR2(), v3 = ruleR3();
                n++; gn++; tN[tk]++;
                if (v2 != exact) { if (v2 == 0) m2++; else b2++; t2[tk]++; }
                if (v3 != exact)
                {
                    if (v3 == 0) m3++; else b3++;
                    t3[tk]++;
                    if (++shown <= 6)
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
        printf("E=%2d (turn=%2d) : %10lld パターン | R2 不一致 %8lld | R3 取%6lld 誤%6lld%s\n",
               E, turn, n, m2 + b2, m3, b3, (m3 == 0 && b3 == 0) ? "  ← R3 完全一致" : "");
        g2 += m2 + b2; g3m += m3; g3b += b3;
    }
    printf("\n合計 %lld パターン | R2 不一致 %lld | R3 取りこぼし %lld 誤断定 %lld\n", gn, g2, g3m, g3b);
    printf("\n[高い柱(h>=3)の本数による層別]\n");
    for (int k = 0; k <= 5; k++) if (tN[k])
        printf("  tall=%d : %10lld パターン  R2 不一致 %8lld (%.2f%%)  R3 不一致 %8lld\n",
               k, tN[k], t2[k], 100.0 * t2[k] / tN[k], t3[k]);
    return 0;
}
