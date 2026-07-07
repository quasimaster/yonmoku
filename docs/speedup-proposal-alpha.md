# main_alpha.cpp 高速化提案書

対象: `code/main_alpha.cpp` および依存ヘッダ(`board.hpp`, `ai_player.hpp`, `evaluate_alpha.hpp`, `common.hpp`, `game.hpp`)

本書は、現行の αβ探索 AI の計算速度をさらに向上させるための改善案を、
**期待効果 × 実装コスト** の観点から優先度順に整理したものである。
コードの変更は行っておらず、提案のみをまとめている。

---

## 1. 現状整理

### 実装済みの高速化手法

| 手法 | 実装箇所 |
|---|---|
| bitboard(64bit 2枚: `Me`, `You`) | `board.hpp` `struct Board` |
| αβ法(negamax 形式) | `ai_player.hpp` `AIPlayer::evaluate_board` |
| reach(リーチ)による強制手枝刈り | `evaluate_board` 先頭・`Board::reach` |
| 相手に勝ち点を献上する手の除外(`hand &= ~(r >> 16)`) | `ai_player.hpp:71` |
| 静的 move ordering(核 → 2〜4段目 → 1段目の3段階マスク) | `common.hpp` `move_order` |
| 動的 move ordering(深いノードで全合法手を3手読みしてソート) | `evaluate_board` の「4手読みパート」 |
| NDEBUG による assert 無効化 | `main_alpha.cpp:1` |
| OpenMP による複数ゲーム並列(自己対戦データ生成) | `main_alpha.cpp` |

### ホットパスの構造

```
AIPlayer::move (root)
 └ evaluate_board (再帰、探索ノード数の大半)
     ├ board.valid_move()                … シフト演算のみ(軽い)
     ├ Board::reach(Me), reach(You)      … 毎ノード2回。斜め28ライン分のループを含む
     ├ (level>=8) 全合法手の3手読み + vector 確保 + sort
     ├ place_fast_clone + Board::win     … win は NDEBUG 下では assert 専用
     └ (葉) evaluate_func(board)
         ├ Board::reach(Me), reach(You)  … ★直前に計算済みのものを再計算
         ├ board.count()                 … 76ライン × popcount 2回
         ├ 76ライン走査(makeT 検出)
         └ board.turn()                  … 各サブ関数で重複呼び出し
```

探索は深さ8〜22手に達するため、**葉ノード(評価関数)と reach の呼び出し回数が支配的**。
また置換表が無いため、手順前後で合流する同一局面を毎回読み直している。

### 現行ビルド

```bash
g++ -std=c++17 -O2 -fopenmp code/main_alpha.cpp -o yonmoku_alpha
```

`-O3` / `-march=native` / LTO は未使用。

---

## 2. 提案一覧(優先度順)

### 提案1【効果: 大 / コスト: 中】置換表(トランスポジションテーブル)+ 反復深化

**最も効果が大きい未実装の定番手法。**

立体四目並べは「同じマスの集合に同じ順序グループで石を置く」手順前後が極めて多く、
探索木の異なる枝が同一局面に合流する。現状はそれを毎回読み直している。
置換表の導入で探索ノード数が **数分の1〜1桁** 減ることが期待できる
(深さが深いほど効果が大きい。turn>=39 で深さ22 の終盤読みが最大の受益者)。

- **ハッシュ**: 局面は `(Me, You)` の128bitで一意。Zobrist ハッシュでもよいが、
  `hash = Me * 定数1 ^ You * 定数2` のような直接ミックスでも十分
  (place のたびに増分更新できる Zobrist の方が置換表以外にも流用しやすい)。
- **エントリ**: `{ key(検証用), depth, value, bound(EXACT/LOWER/UPPER), best_move(6bit) }`
  を 16 byte 程度に詰め、2^22〜2^24 エントリの固定長配列 + 単純上書き(depth 優先)で十分。
- **反復深化**: 深さ 2, 4, …, level と浅い方から反復し、置換表の best_move を
  常に最初に読む。これにより現行の「3手読み事前ソート」(提案4参照)がほぼ無償で置き換わる。
- **注意(OpenMP 並列との両立)**: `main_alpha.cpp` の自己対戦データ生成は
  複数ゲームを OpenMP で並列実行するため、置換表は `thread_local`(スレッド毎に確保)にするか、
  ロックレス XOR トリック(Hyatt 方式)を使う。まずは thread_local が安全で簡単。
  メモリは「エントリ数 × スレッド数」になるため、8スレッドなら 2^22 エントリ(64MB/枚)程度から。
- **注意(評価値の手数依存)**: 現行の勝ち評価 `INF - board.turn()` は turn を含むため
  そのまま格納してよいが、評価関数も turn_bucket に依存する。局面が同じなら turn も
  同じ(石数で決まる)ので問題ないことを確認済み。

対象: `ai_player.hpp` `evaluate_board` / 新規 `tt.hpp`

### 提案2【効果: 中(即効) / コスト: 小】葉ノードでの reach 二重計算の排除

`evaluate_board` は葉に到達する直前に `Board::reach(board.Me)` と `Board::reach(board.You)`
を計算しているが(`ai_player.hpp:64,68`)、その直後に呼ぶ
`evaluate_pointfir_cont_layer_intersection`(`evaluate_alpha.hpp:339-346`)が
**同じ盤面に対して reach を Me/You 双方ゼロから再計算している**。

```cpp
// evaluate_alpha.hpp:339 現状
inline int evaluate_pointfir_cont_layer_intersection(const Board &board)
{
    const unsigned long long rMe  = Board::reach(board.Me) & ~board.You;  // 再計算
    const unsigned long long rYou = Board::reach(board.You) & ~board.Me;  // 再計算
    ...
}
```

**改善案**: 評価関数のシグネチャを `evaluate(const Board&, ull rMe_raw, ull rYou_raw)` に変え、
`evaluate_board` 内で計算済みの reach を渡す。呼び出し規約の変更のみで、
評価値は完全に一致する(挙動不変)。葉ノードでは reach が処理時間の大きな割合を
占めるため、**葉あたり reach 2回分(斜め28ラインループ2周を含む)がまるごと消える**。

同様に `board.valid_move()` も `evaluate_board` 側で計算済み(`hand`)なので渡せる
(現状 `hand` 引数は `reach_layer_intersection` 内で未使用のため、整理も兼ねる)。

対象: `evaluate_alpha.hpp:339-355`, `ai_player.hpp:70`

### 提案3【効果: 中 / コスト: 小】動的 ordering の vector をスタック固定長配列に

`evaluate_board` の「4手読みパート」と `move` の root ordering は、
ノード毎に `vector<pair<int, unsigned long long>> dynamic` を確保している
(`ai_player.hpp:81, 174`)。level>=8 のノードすべてでヒープ確保+解放が走る。

合法手は**最大16手**と上限が固定なので、

```cpp
array<pair<int, unsigned long long>, 16> dynamic;
int n = 0;
// dynamic[n++] = make_pair(ev, bit);
sort(dynamic.begin(), dynamic.begin() + n, greater<>());
```

とするだけでヒープ確保が消える。挙動は完全に不変。
(さらに言えば、αβでは全ソートは不要で、上位から取り出すだけなら選択ソート的に
「その都度最大を探す」方が early cutoff 時に無駄がないが、n≤16 なので差は小さい)

対象: `ai_player.hpp:81-101, 174-196`

### 提案4【効果: 中 / コスト: 中】killer move / history heuristic による安価な ordering

現行の動的 ordering は「深いノード(level>=8)で**全合法手に3手読み**」を行っており、
これ自体がノードあたり最大16回の深さ3探索という大きな固定費になっている。

- **killer move**: 各深さ(ply)ごとに「直近で β カットを起こした手」を2つ記憶し、
  次の兄弟ノードで最初に試す。記憶は `killer[ply][2]` の配列1本、コストほぼゼロ。
- **history heuristic**: `history[64]` に「カットを起こした手 += depth²」を蓄積し、
  ソートキーに使う。こちらも配列1本。

3手読み事前ソートと同等以上のカット率を、探索コストなしで得られることが多い。
提案1(置換表 best_move)+ killer + 静的 `move_order` の組み合わせが定石で、
その場合3手読み事前ソートは撤去するか「置換表ミス時のみ」に限定できる。

対象: `ai_player.hpp` `evaluate_board`

### 提案5【効果: 中 / コスト: 中】PVS(Principal Variation Search)化

root(`move`)は既に `evaluate_board(b, ..., -INF, -mx + 1)` と上界を絞った探索を
しているが、内部ノードは素の αβ。ordering が良い(提案1・4導入後)前提で、

- 最初の手だけ `(-beta, -alpha)` のフルウィンドウ
- 2手目以降は `(-alpha-1, -alpha)` の null window → fail high なら再探索

とする PVS で、カット率がさらに向上する。

**注意**: root では「最善値と同点の手をすべて集めてランダム選択」する現仕様
(`ai_player.hpp:224-225`)があるため、root だけは null window を `(-mx-1, -mx+1)` に
して「同点(=mx)も fail high 扱いで検出 → 再探索で確定」とすれば仕様を維持できる。

対象: `ai_player.hpp` `evaluate_board`, `move`

### 提案6【効果: 中 / コスト: 極小(ビルドのみ)】コンパイルオプションの強化

コードを一切変えずに試せる。

```bash
g++ -std=c++17 -O3 -march=native -flto -fopenmp code/main_alpha.cpp -o yonmoku_alpha
```

- `-march=native`: `h & -h` が BLSI、`__builtin_ctzll` が TZCNT、
  `__builtin_popcountll` が POPCNT の**1命令**にコンパイルされる
  (現状はベースライン x86-64 向けで popcount がライブラリ的展開になっている可能性がある)。
  ホットパスは popcount/ctz/blsi だらけなので効果が出やすい。
- `-O3`: ループアンロール・自動ベクトル化の強化。76ライン走査系に効く。
- `-flto`: 単一 TU ビルドなので効果は限定的だが害はない。
- さらに踏み込むなら **PGO**(`-fprofile-generate` で数ゲーム実行 → `-fprofile-use`)。
  分岐の多い探索コードでは 5〜15% 程度の改善が出ることがある。

配布用バイナリが必要な場合は `-march=native` の代わりに `-march=x86-64-v3`(AVX2 世代)を推奨。

### 提案7【効果: 中〜大 / コスト: 大】評価関数の定数倍高速化

葉ノードの評価関数は以下のコストを持つ:

1. `board.count()`: 76ライン × (AND ×2 + popcount 最大2回)(`board.hpp:195-205`)
2. makeT 検出: 76ライン再走査 + count==±2 のラインで内側 while ループ(`evaluate_alpha.hpp:43-95`)
3. `board.turn()`: `evaluate_pointfir` / `continuous_fir` ×2 / `reach_layer_intersection` で
   計4回以上の popcount 重複呼び出し

改善案(独立に適用可能):

- **(7a) turn の集約**: `evaluate_*_cont_layer_intersection` で turn と turn_bucket を
  1回だけ計算して各サブ関数に渡す。小さいが確実。
- **(7b) pext + テーブル参照**: BMI2 の `_pext_u64(Me, LINES[i])` でライン内の自石配置を
  4bit に圧縮できる。`(pext(Me,L) << 4) | pext(You,L)` の 8bit をインデックスに、
  「そのラインの stdweight 寄与」「count==±2 か」を **256 エントリの事前計算テーブル**で
  引けば、count() の分岐と popcount が消える(turn_bucket 4種 × 256 の小テーブル)。
  ※ Zen3 以降 / Intel では pext は 3 サイクル。Zen1/2 ではマイクロコードで遅いため、
  実行環境の確認が必要(`-march=native` とセットで)。
- **(7c) ライン充填数の増分更新**: 究極的には、`place` のたびに「その着手マスを通る
  ライン(マスごとに 4〜7 本、事前テーブル化可能)」だけ count を ±1 更新する構造にすれば、
  76ライン走査自体が探索から消える。`Board` に `int8_t count[76]` を持たせて
  `place_fast_clone` で差分更新する。reach も同様に増分化できる
  (「count が +3 になったラインの空きマス」を更新)。
  効果は最大だが、`Board` のコピーコストが 16B → 96B 程度に増えるトレードオフが
  あるため、**ベンチマークで往復比較すべき**(浅い探索ではコピー増が勝つ可能性あり)。

対象: `evaluate_alpha.hpp` 全体, `board.hpp` `count`, `reach`

### 提案8【効果: 小 / コスト: 極小】その他の細かい削減

- **NDEBUG 下で不要な win 呼び出しの整理**: `Board b = board.place_fast_clone(bit);
  enum State r = Board::win(b.You); assert(r == State::Continue);` のパターン
  (`ai_player.hpp:92-95` ほか多数)は、NDEBUG 時に `r` が未使用になる。
  `win` は純関数なので -O2 で除去される**はず**だが、保証はないため
  `#ifndef NDEBUG` で囲むかコメントアウトして、生成コードから確実に消すのが安全。
  (アセンブリ確認 or ベンチで差が無いことの確認だけでもよい)
- **reach の斜め28ラインループのアンロール**: `board.hpp:133-137` の
  `for (i = 48; i < 76)` は LINES がグローバル配列のためメモリロードが挟まる。
  z/x/y 方向と同様のシフト演算パターン化は複雑になるため、
  まずは `LINES` を `alignas(64)` にしてキャッシュライン整列するだけでもよい。
- **`Board::win` の早期 return 順**: 実戦で最も多い勝ち筋(統計を取って)を
  先頭に並べ替えると分岐予測に有利。ただし win は探索中ほぼ呼ばれない
  (reach で先に検出される)ため優先度は低い。

### 提案9【効果: 大(終盤限定)/ コスト: 大・任意】発展的な施策

- **終盤専用の勝敗ソルバー**: turn>=39 で深さ22 まで読む現状は、実質「終盤の完全読み」。
  この領域は評価関数を捨てて勝ち/負け/引き分けの3値探索(+置換表)に切り替えると、
  ウィンドウが `(-1, 1)` 固定になりカット率が劇的に上がる。
  弱解決向けの proof-number search まで行かずとも、3値 αβ + 置換表だけで大きい。
- **盤面対称性の利用**: この盤は x反転・y反転・xy対角の8対称。序盤の置換表キーを
  「8対称の正規形(最小値)」にすると序盤の探索が最大1/8に圧縮できる。
  正規化コストが毎ノードかかるため、序盤(石数が少ない)のみ適用が現実的。
- **Lazy SMP(1ゲーム内の並列探索)**: 現在の OpenMP 並列は「ゲーム間」並列であり
  データ生成のスループットには十分。人間対戦(`main_alpha.cpp` 現行設定)の
  応答速度を上げたい場合のみ、共有置換表 + 複数スレッド同時探索(Lazy SMP)を検討。
  提案1の置換表が前提。

---

## 3. 計測・検証方法

**各施策は必ず個別に、同一条件で計測してから採否を決めること。** 手順:

1. **ベンチマークハーネスの作成**(最初にやる):
   - `evaluate_board` 内に `thread_local long long node_count` を置いてノード数を計測
     (計測ビルドのみ有効化する `#ifdef BENCH` で囲む)。
   - 固定の代表局面セット(序盤・中盤・終盤の 10〜20 局面。既存の自己対戦棋譜
     `record_*.csv` から再現できる)に対し、固定深さで探索して
     「総ノード数」「総時間」「nps(nodes per second)」を出力する `bench` モードを
     `main_alpha.cpp` に追加。乱数は `mt19937 rng;`(シード固定、`common.hpp:21` の
     コメントアウト側)を使い再現性を確保。
2. **効果の切り分け**:
   - 置換表・ordering 系(提案1,4,5)→ **ノード数の減少**で評価
   - 評価関数・reach 系(提案2,7)と ビルド系(提案6)→ **nps の向上**で評価
3. **正しさの検証**:
   - 提案2,3,6 は挙動不変のはずなので、シード固定で改善前後の自己対戦数ゲームの
     着手列・評価値列(`evaluatesfir_tmp` 等)が完全一致することを確認。
   - 提案1,4,5 は探索順が変わるため評価値は一致するが選択手が変わり得る。
     固定局面での「root の評価値」が一致することを確認する。
4. **対局強度の最終確認**: 大きな変更(提案1,7c,9)の後は、旧バージョンとの
   対戦(先後入れ替え数百局、`set_random` で揺らぎ付与)で強度が落ちていないことを確認。

---

## 4. 推奨する着手順序

| 順 | 施策 | 理由 |
|---|---|---|
| 0 | ベンチマークハーネス(§3) | 以降すべての判断基準になる |
| 1 | 提案6: ビルドフラグ | コード変更ゼロで即効 |
| 2 | 提案2: reach 二重計算排除 | 挙動不変・低リスク・葉ノード直撃 |
| 3 | 提案3: vector → 固定長配列 | 挙動不変・低リスク |
| 4 | 提案1: 置換表 + 反復深化 | 最大の伸びしろ。ここに最も工数を割く |
| 5 | 提案4,5: killer/history + PVS | 置換表と相乗。3手読み事前ソートの撤去判断 |
| 6 | 提案7: 評価関数テーブル化/増分化 | 置換表導入後もなお葉が支配的なら |
| 7 | 提案9: 終盤ソルバー等 | 必要に応じて |

まず 0〜3 だけでも「無リスクで数十%」、4〜5 で「ノード数の桁改善」が現実的な目標値。
