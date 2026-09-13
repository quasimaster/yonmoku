# match_weights — 評価関数バージョン同士の対戦ハーネス

2 つの重みファイル(= 評価関数のバージョン)を AI 同士で対戦させ、勝率で強さを比べるツール。
マルチスレッドで動く。

- ソース: `code/match_weights.cpp`
- 重みファイルの形式: `weights/README.md`
- 設計の経緯: `docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md` §2.6

探索・評価・盤面・置換表は、教師データ生成(`main_alpha_pvs_eval_inc_tbl_id_w.cpp`)と同じヘッダを使う。
違うのは重みだけ。

## ビルド

リポジトリ直下で実行する。

```bash
g++ -std=c++17 -O2 -DBENCH code/match_weights.cpp -o match_weights.exe
```

| オプション | 意味 |
|---|---|
| `-DBENCH` | 探索ノード数を数えて出力する。外すと `nodes=0` になるだけで対戦結果は変わらない |
| `-DUSE_ENDGAME_R2=0` | 終盤ロジック R2 を無効にする(既定 1) |
| `-DUSE_ENDGAME_CUT=0` | 終盤の打ち切りを無効にする(既定 1) |
| `-DUSE_ASSERT` | assert を有効にする(既定は無効。遅くなる) |

## 使い方

```
match_weights <A> <B> hirate   <総局数>                 [並列数=1] [level=10]
match_weights <A> <B> openings <1スレッドあたりの周回数> [並列数=1] [level=10]
```

| 引数 | 内容 |
|---|---|
| `<A>` `<B>` | 重みファイルのパス(例: `weights/alpha/ver8_2.txt`)。`builtin` と書くと組み込み既定値(ver7.2 相当) |
| `hirate` / `openings` | 対局の始め方(下記) |
| `<総局数>` | hirate のとき。**偶数**で指定する |
| `<1スレッドあたりの周回数>` | openings のとき。全定跡を何周するか |
| `[並列数]` | スレッド数。省略時 1 |
| `[level]` | 読みの深さ。1〜64。省略時 10 |

重みファイルと定跡ファイルは、実行ディレクトリ・`../`・`../../` の順に探す。
リポジトリ直下からでも `code/` からでも実行できる。

### hirate — 平手

初期局面から対局する。

- 総局数を「A 先手 1 局 + B 先手 1 局」の組に分け、各スレッドへ均等に配る。
  組数が並列数で割り切れないときは、余りを先頭のスレッドから 1 組ずつ足す。
- 各スレッドは A 先手 → B 先手 → A 先手 … と交互に打つ。
  このため**どのスレッドでも A 先手と B 先手が同数**になる。
- 並列数が組数(総局数 ÷ 2)より多いときは、組数まで減らす(その旨を表示する)。

```bash
# 平手で合計 10000 局(A 先手 5000 / B 先手 5000)を 16 並列、level 10
./match_weights.exe weights/alpha/ver8_2.txt weights/alpha/ver8_2_5.txt hirate 10000 16 10
# → 各スレッド 625 局
```

### openings — 定跡から

`unique_opening/unique_openings_4.txt` の定跡(4 手まで打った局面、重複なし 2925 本)から対局する。

- 各スレッドが**全定跡**を指定周回数だけ回す。定跡の一部だけを使う指定はできない。
- 定跡 1 本につき A 先手と B 先手の 2 局を打つ。
- 総局数 = 並列数 × 周回数 × 2925 × 2

```bash
# 16 スレッドがそれぞれ全定跡を 1 周 → 16 × 1 × 2925 × 2 = 93600 局
./match_weights.exe weights/alpha/ver8_2.txt weights/alpha/ver8_2_5.txt openings 1 16 10
```

### 使い分け

| 見たいもの | モード |
|---|---|
| 実際の対局(初期局面から)でどちらが強いか | `hirate` |
| 序盤の形に偏らず、いろいろな局面での強さ | `openings` |

## 出力

実際の出力例(`hirate 16 8 3`)。

```
A = ver8.2 (weights/alpha/ver8_2.txt)
B = ver8.2.5 (weights/alpha/ver8_2_5.txt)
config: mode=hirate total_games=16 threads=8 (per thread 2..2) level=3
        USE_ENDGAME_R2=1 USE_ENDGAME_CUT=1 seed=5489+thread
[t04] hirate #     0 A-black: moves=25 A win     0.345 sec  nodes=     1072146  (1/16)
[t04] hirate #     1 B-black: moves=60 A win     4.939 sec  nodes=    12954684  (2/16)
[t03] hirate #     0 A-black: moves=57 A win    17.094 sec  nodes=    36243187  (3/16)
...
--------
[t00] A勝 1 / B勝 1 / 分 0
[t01] A勝 1 / B勝 1 / 分 0
...
A 先手: A勝 4 / B勝 4 / 分 0
B 先手: A勝 5 / B勝 3 / 分 0
合計  : A勝 9 / B勝 7 / 分 0  (16 局)
A の勝率(引分 0.5): 56.25 %
wall : 506.961 sec
total: 1396.185 sec (全局の対局時間の和)
nodes: 3231007492
```

### 1 局ごとの行

終わった順に出力するので、スレッドの行が入り混じる。

| 項目 | 意味 |
|---|---|
| `[t04]` | スレッド番号 |
| `hirate #     0` | そのスレッド内での対局番号(平手) |
| `lap 0 book  123` | 何周目の何番目の定跡か(openings のとき) |
| `A-black` / `B-black` | A が先手の局 / B が先手の局 |
| `moves=` | 定跡の手も含めた総手数 |
| `A win` / `B win` / `draw` | 勝者(**色ではなくモデル**で表示) |
| `sec` / `nodes=` | その局にかかった時間 / 探索ノード数(両者の合計) |
| `(3/16)` | 全体の進捗 |

### 集計

| 行 | 意味 |
|---|---|
| `[tNN] A勝 / B勝 / 分` | スレッドごとの結果 |
| `A 先手:` / `B 先手:` | 手番別の結果。先手有利の偏りを見る |
| `合計` / `A の勝率` | 全体の結果。勝率は引分を 0.5 勝として計算 |
| `wall` | 実際にかかった時間 |
| `total` | 全局の対局時間の合計(並列なので wall より大きい) |

### 勝率の誤差の目安

N 局で勝率 p のとき、95% の幅はおよそ ±1.96 × √(p(1−p)/N)。

| 局数 | 勝率 50% 付近の誤差 |
|---|---|
| 100 | ±9.8 % |
| 1000 | ±3.1 % |
| 10000 | ±1.0 % |

ただし下の「乱数と再現性」のとおり、平手で局数を増やしても、まったく同じ棋譜が何度も出ることがある。
重複の多さによっては、実際の誤差はこの表より大きい。

### ログを保存する

画面にも出しつつファイルに残すなら `tee`(PowerShell では `Tee-Object`)を使う。
**既存のログと同じ名前にすると上書きされる**ので、毎回新しい名前にすること。

```bash
# Git Bash
./match_weights.exe weights/alpha/ver8_2.txt weights/alpha/ver8_2_5.txt hirate 10000 16 10 2>&1 | tee match_ver8_2_vs_ver8_2_5_hirate10000.log
```

```powershell
# PowerShell(先に 1 行目を実行しないと日本語が化ける。下の「文字コード」参照)
[Console]::OutputEncoding = [Text.Encoding]::UTF8
.\match_weights.exe weights/alpha/ver8_2.txt weights/alpha/ver8_2_5.txt hirate 10000 16 10 | Tee-Object -FilePath match_ver8_2_vs_ver8_2_5_hirate10000.log
```

### 文字コード

出力は UTF-8。

- **cmd / PowerShell にそのまま表示する場合:** 日本語 Windows のコンソールは既定で CP932(Shift_JIS)なので、そのままだと化ける。
  そのため `match_weights` は実行中だけコンソールの出力コードページを UTF-8 に切り替え、終了時(Ctrl+C を含む)に元へ戻す。
  利用者側の設定は要らない。
- **PowerShell でパイプ(`|`)に通す場合:** 表示を担当するのが PowerShell になり、PowerShell が自分の設定(`[Console]::OutputEncoding`、既定 932)で出力を読み直す。
  プログラム側では防げないので、実行前に `[Console]::OutputEncoding = [Text.Encoding]::UTF8` を設定する(その PowerShell ウィンドウを閉じるまで有効)。
- **Git Bash や、`>` でファイルへ書き出す場合:** UTF-8 のまま扱われるので問題ない。

## 乱数と再現性

- 両プレイヤーともランダム手は打たない(`set_random(0)`)。
- 棋譜がばらつく原因は **評価値が同点の最善手が複数あるとき、その中から乱数で選ぶ** ことだけ。
- 乱数はスレッドごとに独立していて、スレッド t の初期値は `5489 + t`。
  **同じ引数(並列数も含む)で実行すれば、毎回同じ結果になる。**
- 並列数を変えるとスレッドへの配り方と乱数が変わるので、結果も変わる。
- 並列数 1 の openings モードは、改修前の `match_weights`(逐次版)と同じ棋譜になる(手数・勝敗・ノード数の一致を確認済み)。

### 仕組み(ヘッダを触る人向け)

`code/ai_player_pvs_inc_id.hpp` の乱数呼び出しは `AI_RNG()` マクロを通る。
既定では `common.hpp` のグローバル `rng` になるので、ほかのプログラムの動作は変わらない。
`match_weights.cpp` は include の前に `#define AI_RNG g_match_rng`(thread_local)を定義して、スレッドごとの生成器に差し替えている。

## 時間とメモリの目安

- **時間:** 1 局の時間は level より終盤の読み切りでほぼ決まり、ばらつきが大きい。
  level 3 でも 1 局 0.3〜470 秒だった。大きな回数を回す前に、`hirate 64 16 10` などで所要時間を測っておく。
- **CPU:** このマシンは 16 論理コア。並列数を 16 より多くしても速くならない。
- **メモリ:** AI 1 体の置換表が 64MB で、1 スレッドあたり 2 体 = 128MB。
  16 並列なら約 2GB。

## 補足

- 先手番の AI は重みファイルの先手用エントリ(`fir`)、後手番の AI は後手用エントリ(`sec`)を使う。
  「A 先手」の局なら、A の `fir` と B の `sec` の対戦になる。
- 重みファイルが読めないときは、組み込み既定値を使わずにエラー終了する(どのモデルで打ったか分からなくなるのを防ぐため)。
- 引数が間違っているとき(総局数が奇数、mode の綴り違い、並列数や level が範囲外)は、メッセージを出して終了コード 2 で終わる。
