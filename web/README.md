# 立体四目並べ Web 版

既存の C++ 探索エンジン(`code/*.hpp`)を Emscripten で WebAssembly 化し、
Three.js の 3D UI から対局できるようにしたもの。**サーバ不要の静的サイト**。

設計: `docs/設計書/Web公開/implementation-plan-web-ui-3d.md`
実測: `docs/実行結果/benchmark-results-wasm.md`

**モデル選択と読み手数スケジュール**(2026-09-20 追加)
設計: `docs/設計書/Web公開/implementation-plan-model-select-and-custom-depth.md`
実測: `docs/実行結果/benchmark-results-web-model-select.md`

- **モデル** = (探索エンジン, 重みバージョン)の組。`weights/` をまるごと WASM に埋め込んでいる。

  | | 重み | 探索 |
  |---|---|---|
  | `alpha` | ver7.2(組み込み既定値・**既定**) / ver8.1 / ver8.2 / ver8.2.5 | `main_alpha_pvs_eval_inc_tbl_id_w` 相当 |
  | `core` | ver1.0 | `main_core2` 相当 |

  重みを足すときは `weights/alpha/` などに置き、`code/web/engine_api2.cpp` の `MODELS[]` に 1 行足して再ビルドする。
- **評価値**は画面上部に大きく出る(将棋中継の評価値表示と同じ読み方。黒視点)。
- **読み手数**: 「n 手目以降 N 手読み」を最大 8 行まで自由に指定できる。N は 2〜30 の偶数のみ
  (評価関数が偶数手読みを前提にしているため)。難易度プリセットを選ぶと表に流し込まれ、
  そこから編集すると「カスタム」に切り替わる。設定は localStorage に保存される。
- **中止ボタンは無い**。重い設定は 1 手に数分かかりページが応答しなくなるので、
  UI が事前に警告を出す(core はしきい値が 1 段低い)。

**研究モード**(2026-09-20 追加)
設計: `docs/設計書/Web公開/implementation-plan-research-analysis.md`
実測: `docs/実行結果/benchmark-results-web-research.md`

画面上部の「研究モード」にチェックを入れると、対局ではなく**任意局面の形勢判断**ができる。

- **AI は自動で指さない**。白黒の両方を自分でクリックして、調べたい局面まで並べる。
  「一手戻す」は **1 手ずつ**(対局モードの「一手戻る」は AI 手 + 自分の手の 2 手戻し)。
- 「解析開始」で **8 手読みから 2 手ずつ深化**し、1 反復ごとに結果が届く。
  **読み手数に上限は無い**。終わるのは次の 3 つだけ:
  - 人が「停止」を押した
  - 空きマス数を超えた(= 全読み。これ以上深めても値は変わらない)
  - 勝敗を読み切った
- **上位 3 手**(1〜5 手に変更可)の評価値と黒勝率を出す。値は**厳密**で、
  盤面には 1 位 = 金 / 2 位 = 銀 / 3 位 = 銅のリングが出る。
- 評価値は**常に黒視点**。読み切ったときは数字ではなく「黒 必勝 / 白 必勝」と出る。

> **停止は反復の合間にしか効かない。** WASM の探索は同期実行で Worker を完全にブロックするため、
> 走っている反復が終わるまで停止ボタンは効かない。そのため「1 反復の上限」(**既定 10 分**)がある。
> 期限に達すると、そこまでの最善を「途中経過」として出して止まる。無制限も選べるが、
> 深い反復に入ると停止できない時間が青天井になる。

> 「毎回置換表をクリア」を外していると(既定)、前の深さの結果を使い回すので速い代わりに、
> 値は「N 手読みちょうど」ではなくなる。厳密な N 手読みの値が要るときはチェックを入れる。

補足(研究上の注意):

- **N は偶数のみ**。評価関数が偶数手読みを前提にしているため。
- **候補が絞られることがある**。自分に即勝ちがあれば探索せずその手を返し、
  相手にリーチがあれば候補は阻止手のみになる(エンジンの `move()` と同じ規則)。
  どちらも候補手カードに明記される。
- 研究モードを抜けて対局に戻るとき、**先後用の評価テーブルと置換表は元に戻される**ので、
  対局の強さに影響しない。

## 構成

```
web/
├── index.html          UI
├── style.css
├── main.js             Three.js シーン + HUD(メインスレッド)
├── worker.js           探索エンジンを動かす Web Worker
├── yonmoku.js          Emscripten glue      ← 生成物(コミットする)
├── yonmoku.wasm        エンジン本体          ← 生成物(コミットする。core 重みを埋め込み済み)
├── exports.json        WASM から公開する関数一覧
├── package.json        Node からのテスト用({"type":"module"})
├── build.ps1           ビルドスクリプト
└── vendor/             Three.js(CDN 依存を避けて同梱)
```

エンジン側のソースは `code/web/engine_api2.cpp`(旧: `engine_api.cpp` / `engine_api_w.cpp` も比較用に残してある)。
探索・評価・盤面・置換表は **CLI 版と同一のヘッダをそのまま include** している。

- alpha は `main_alpha_pvs_eval_inc_tbl_id_w.cpp` と同じ `_w` 経路
  (非 `_w` の `evaluate_alpha_inc_tbl.hpp` は `flag_tbl[256]` が衝突して core と同居できない)
- core は `main_core2.cpp` と同じ `tt2` / `board_inc2` / `ai_player_pvs_inc_id2` / `evaluate_core2`
- 置換表は一律 22 bit(64 MB)。同時に生かすのは片方だけ

## ローカルで動かす

```powershell
# 1. ビルド(emsdk が必要。既定は C:\emsdk)
powershell -ExecutionPolicy Bypass -File web\build.ps1

# 2. 配信(file:// では ES module / Worker が動かないので HTTP で開くこと)
python -m http.server 8777 --directory web
#   → http://127.0.0.1:8777/
```

`emsdk` の導入:

```powershell
git clone https://github.com/emscripten-core/emsdk.git C:\emsdk
C:\emsdk\emsdk.bat install latest
C:\emsdk\emsdk.bat activate latest
```

> `upstream\emscripten\` に `emcc.bat` などのラッパが無いとシステムライブラリのビルドで
> `FileNotFoundError [WinError 2]` が出る。作り方は設計書 §12.2 を参照。

> 同じ理由で `--embed-file`(core の重みを埋め込むのに使う)は
> `upstream\emscripten\tools\file_packager.bat` を要求する。無ければ `build.ps1` が自動生成する。

> `build.ps1` は **UTF-8 BOM 付き**で保存してある。**BOM を外さないこと。**
> BOM が無いと Windows PowerShell 5.1 は cp932 として読み、日本語が化けるうえ、
> **コメント行が `。` で終わると改行まで食われて次の行が丸ごと消える**
> (`$src = ...` が無効化され、原因の分からないビルド失敗になった)。

## テスト

| コマンド | 内容 |
|---|---|
| `node web/test_node.mjs` | WASM の API 動作確認 + プロファイル別の速度 |
| `node web/test_worker.mjs` | Worker のメッセージプロトコル(ブラウザ不要) |
| `node web/bench_fixed.mjs` | native と同一局面での速度比較 |
| `node build/e2e/e2e.mjs` | 実ブラウザ E2E(描画・クリック着手・透視・undo・難易度) |
| `node build/e2e/e2e_endgame.mjs` | 実ブラウザ E2E(終局・勝利ライン・結果表示) |
| `node build/e2e/e2e_research.mjs` | 実ブラウザ E2E(研究モード・両色着手・反復深化・上位 3 手・停止) |

E2E は `build/e2e` で `npm i puppeteer-core` 済みであること、
および上記のローカルサーバが 8777 で動いていることが前提。

native 側:

```
g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
    code/web/engine_api.cpp code/web/test_engine_api.cpp -o build/test_api.exe
```

研究モードの API(`code/web/engine_api2.cpp`):

```
g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
    -DUSE_ENDGAME_R2=1 -DUSE_ENDGAME_CUT=1 \
    code/web/engine_api2.cpp code/web/test_engine_api2.cpp -o build/test_api2.exe
```

## デプロイ(Cloudflare Pages)

**公開先: https://yonmoku.pages.dev/** (2026-08-30 初回デプロイ済み)

生成物(`yonmoku.js` / `yonmoku.wasm`)を**コミットする**方針なので、Pages 側でのビルドは不要。

### 現在の方式: Wrangler の直接アップロード

```powershell
$env:CLOUDFLARE_ACCOUNT_ID = "<Cloudflare の Account ID>"   # dash.cloudflare.com の URL に含まれる 32 桁
npx wrangler pages deploy web --project-name yonmoku --branch main --commit-dirty=true
```

初回のみ `npx wrangler login`(既定ブラウザで OAuth 同意)と
`npx wrangler pages project create yonmoku --production-branch main` が必要。

> Cloudflare が `account:read` スコープを付けないことがあり、その場合 wrangler は
> アカウント ID を自動取得できない。上記のとおり `CLOUDFLARE_ACCOUNT_ID` を明示すること。

> `wrangler pages deploy` は `.assetsignore` を**解釈しない**。`web/` 配下は
> テストスクリプトや README も含めて全部が公開される。除外したい場合は
> 配信用ディレクトリを別に用意してそこを deploy する。

### push で自動デプロイ(GitHub Actions)

`.github/workflows/deploy-pages.yml` が `main` への push を検知し、`web/**` が変わったときだけ
テスト(`test_node.mjs` / `test_worker.mjs`)を通してから `wrangler pages deploy` する。

初回だけ以下の 2 つを登録する(認証情報なので手作業):

1. **Cloudflare API トークン**
   dash.cloudflare.com → 右上プロフィール → **API Tokens** → **Create Token** → **Create Custom Token**
   - Permissions: **Account** / **Cloudflare Pages** / **Edit**
   - Account Resources: 対象アカウント
2. **GitHub の Secrets**
   リポジトリ → Settings → Secrets and variables → **Actions** → New repository secret
   - `CLOUDFLARE_API_TOKEN` … 上で作ったトークン
   - `CLOUDFLARE_ACCOUNT_ID` … dash の URL に含まれる 32 桁

> Cloudflare Pages の **Git 連携(Connect to Git)は使えない**。Direct Upload で作ったプロジェクトは
> あとから Git 連携に切り替えられない仕様のため(切り替えるにはプロジェクトの作り直しが必要)。
> Actions 経由なら既存プロジェクトのまま、`yonmoku.pages.dev` の URL を維持できる。

### 公開後の確認

```
node build/e2e/e2e_prod.mjs   # e2e.mjs の URL を本番に差し替えたもの(build/ は .gitignore 済み)
```

## 既存 CLI との関係

`code/ai_player_pvs_inc_id.hpp` に `YON_DEPTH_TARGET` マクロ(既定値は従来式と同一)を
1 箇所だけ追加している。`-D` を与えない限り既存ビルドの挙動は変わらない
(8 局の着手列・ノード数が一致することを確認済み)。

```
g++ -std=c++17 -O2 -fopenmp code/main_alpha_pvs_eval_inc_tbl_id.cpp -o yonmoku_cli   # 従来どおり
g++ -std=c++17 -O2 -march=native -fopenmp code/main_core2.cpp -o main_core2          # 従来どおり
```

モデル選択・スケジュール対応でも `code/*.hpp` と `code/main_*.cpp` は**一切変更していない**
(`YON_DEPTH_TARGET` フックは `ai_player_pvs_inc_id.hpp` / `ai_player_pvs_inc_id2.hpp` の両方に
既にあるので追加不要だった)。
