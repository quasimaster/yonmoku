# 評価関数の重みファイル

設計: `docs/設計書/評価関数バージョン管理/implementation-plan-eval-weights-file.md`

1 ファイル = 1 モデル(先手用 fir + 後手用 sec の一式、整数 256 個)。
ファイルを差し替えるだけで AI のバージョンを切り替えられる。

## 配置(評価関数の種類ごとにフォルダを分ける)

| フォルダ | 評価関数 | 形式 | 学習コード | 読めるプログラム |
|---|---|---|---|---|
| `weights/alpha/` | 既存(29 本 / バケット) | `version: 1` | `MachineLearning/main_gd_both.cpp` | `match_weights` / `main_alpha_pvs_eval_inc_tbl_id_w` など既存一式、`main_core`(core = 0 として読む) |
| `weights/core/` | 既存 + 核 2 マスの全状態(35 本 / バケット) | `version: 2`(各セクションに `core = 6 個` が増える) | `MachineLearning/main_gd_core.cpp` | `main_core` のみ(既存一式は `version: 2` を拒否する) |

`core` の意味と読み込み規則は `code/core_feature.hpp` / `code/eval_weights_core.hpp` を参照
(設計: `docs/設計書/評価関数パラメータ/investigation-new-eval-features.md` §2.6 D)。

## 命名規約

`verX_Y.txt`(例: `ver7_2.txt`, `ver8_0.txt`)。学習を回すたびに新しい番号で追加し、
既存ファイルは上書きしない(過去モデルとの対戦に使うため)。

## 形式

```
# コメント(# 以降は行末まで無視)
version: 1
name: ver7.2

[fir.bucket0]
stdweight         = 0,-61,-22,0,28,65,0        # 7 個。index 0/3/6 は構造上 0 固定
maketweight       = 53,-13,50,4,22,-50,27,16   # 8 個。0..3 = Me / 4..7 = You
conti_maketweight = 215,189,284,86,160,154     # 6 個。0..2 = Me(T_T,T_W,W_T) / 3..5 = You
layer_me          = 138,476,144                # 3 個。2段/3段/4段
layer_you         = 215,209,192                # 3 個。2段/3段/4段
intersection      = 149,-1104,-29,1327         # 4 個。3段の交点が 1/2/3/4 個のとき
continuous        = 3108                       # 1 個
```

セクションは `[fir.bucket0]` 〜 `[sec.bucket3]` の **32 個すべて**が必要。
1 つでも欠けると読み込みは失敗し、**組み込み既定値へは戻らずエラー終了する**
(どちらのモデルを使ったのか分からなくなる事故を防ぐため)。

`turn_bucket` は先手 `(turn-4)/14`、後手 `(turn-5)/14`。

## alpha/ver7_2.txt の作り方(手打ち禁止)

組み込み既定値との二重管理を避けるため、必ずツールの出力を保存する。

```
g++ -std=c++17 -O2 code/tools/dump_weights.cpp -o dump_weights
./dump_weights > weights/alpha/ver7_2.txt
./dump_weights --check weights/alpha/ver7_2.txt   # builtin() と 256 値一致を確認
./dump_weights --selfcheck                  # dump → load → builtin() の往復検査
```

## 学習結果から新しいモデルを組み立てる

`MachineLearning/main_gd_alpha.cpp` は 1 回の実行で「片側 × 1 バケット」しか求めない
(turn 範囲の指定が `:159-164`、参照する教師値が `evaluatesfir` / `evaluatessec` かで側が決まる)。
1 モデル = **8 回の実行結果**を該当セクションへ貼り合わせる。
同 `:361-378` の転記用出力の 7 行が、上記 7 キーとそのまま 1:1 で対応する。

## loss の記録

`MachineLearning/main_gd_both.cpp` で作ったファイルには、`name:` 行の直後に
学習時の loss が `#` コメントとして 8 行入る。

```
#
# 学習時の loss(交差エントロピーの総和。小さいほど教師値に近い)
# 同じ側・同じバケット同士でのみ比較できる(対象の局面数が違えば大きさも変わる)
# loss  fir.bucket0 (turn  4~17) = 123456.789
...
# loss  sec.bucket3 (turn 47~60) = 56789.123
```

パーサは `#` 以降を行末まで捨てるので、この行があってもなくても読み込み結果は同じ
(`MachineLearning/tools/verify_weights_format.cpp` が毎回それを検査している)。
一度も改善しなかったバケットは数値ではなく `----- (改善なし)` と書かれる。

`code/tools/dump_weights.cpp` の出力には loss は入らない(学習を経ていないため)。

## 使い方

```
# 教師データ生成をこのモデルで回す
./yonmoku_alpha_id --weights weights/alpha/ver8_0.txt

# 旧モデルと対戦させて強さを比べる
#   match_weights <A> <B> hirate   <総局数(偶数)>        [並列数=1] [level=10]
#   match_weights <A> <B> openings <1スレッドあたり周回数> [並列数=1] [level=10]
# 平手で合計 10000 局(先後入れ替え込み)を 16 並列で
./match_weights weights/alpha/ver7_2.txt weights/alpha/ver8_0.txt hirate 10000 16 10

# unique_openings_4.txt の全定跡(2925 本 × 先後 2 局)を 16 スレッドがそれぞれ 1 周
./match_weights weights/alpha/ver7_2.txt weights/alpha/ver8_0.txt openings 1 16 10

# 組み込み既定値を相手にする
./match_weights builtin weights/alpha/ver8_0.txt hirate 1000 16 10
```

## 改行コードについて

`./dump_weights > weights/alpha/ver7_2.txt` を Windows で実行すると CRLF で保存される
(CRT のテキストモード変換)。パーサは `\r` を除去してから解釈するので LF / CRLF の
どちらでも読める。再生成しても同じバイト列になるので、そのままコミットしてよい。
