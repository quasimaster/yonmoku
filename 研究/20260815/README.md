# 2026-08-15 研究一式

論文 `研究/論文/立体四目並べ最終盤の厳密評価理論.md` の §13.2 課題 1
(推測 1 の交差ケース)への回答。

**結論: 推測 1・推測 2 はいずれも偽。正しい成立範囲は turn ≥ 55(これは最良)。**

主報告は **[`研究結果_推測1と推測2の反証.md`](研究結果_推測1と推測2の反証.md)**。

## ファイル

| ファイル | 内容 |
|---|---|
| `研究結果_推測1と推測2の反証.md` | **主報告**。新補題 N1〜N7、主結果 定理 N9、新ゲート `G_X`(定理 N11)、反例 2 件 |
| `shape_enum.cpp` / `shape_enum_result.txt` | ゲートを満たす形状の完全列挙。定理 N4(`E ≤ 26`、1,742,694 形状) |
| `reduced_verify.cpp` | 還元モデル。`check`(定理 N6 の突合)/ `sweep`(全形状の完全検証)/ `sweepfull`(全ラベル割当)/ `sweepx`(ゲート `G_X` つき) |
| `deep_search.cpp` | 実盤面の直接構成による探索。反例 A・B の発見に使用 |
| `counterexample_check.cpp` / `verify_counterexamples.txt` | 反例の**完全に独立した**再検証(`board.hpp` 不使用)。到達手順つき |
| `sweep_E*.log` | 各 `E` の全形状完全検証の結果 |
| `gx_E*.log` | ゲート `G_X` を課した完全検証の結果(すべて反例 0) |
| `cls_E11.log` | `E = 11` の反例 288 個を交差の有無で分類 |
| `反例Bの発見ログ_turn45.log` | 反例 B が最初に見つかったときのログ |

## ビルド・実行

```sh
g++ -O2 -std=c++17 -DNDEBUG -o shape_enum.exe          shape_enum.cpp
g++ -O2 -std=c++17 -DNDEBUG -o reduced_verify.exe      reduced_verify.cpp
g++ -O2 -std=c++17 -DNDEBUG -o deep_search.exe         deep_search.cpp
g++ -O2 -std=c++17 -DNDEBUG -o counterexample_check.exe counterexample_check.cpp

./shape_enum.exe 1 1                 # 形状の完全列挙
./reduced_verify.exe check 55 3000   # 還元定理の突合
./reduced_verify.exe sweep 10        # E=10 の全形状を完全検証(反例 0 = turn 55 の証明)
./reduced_verify.exe sweep 11        # E=11 の全形状(反例 288 = turn 54 の反証)
./reduced_verify.exe sweepx 15 0 -1 1 # ゲート G_X つきの完全検証
./counterexample_check.exe           # 反例 2 件の独立検証
```

`sweep` は反例を見つけると終了コード 1 を返す。
