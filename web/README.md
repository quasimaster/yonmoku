# 立体四目並べ Web 版

既存の C++ 探索エンジン(`code/*.hpp`)を Emscripten で WebAssembly 化し、
Three.js の 3D UI から対局できるようにしたもの。**サーバ不要の静的サイト**。

設計: `docs/設計書/Web公開/implementation-plan-web-ui-3d.md`
実測: `docs/実行結果/benchmark-results-wasm.md`

## 構成

```
web/
├── index.html          UI
├── style.css
├── main.js             Three.js シーン + HUD(メインスレッド)
├── worker.js           探索エンジンを動かす Web Worker
├── yonmoku.js          Emscripten glue      ← 生成物(コミットする)
├── yonmoku.wasm        エンジン本体          ← 生成物(コミットする)
├── exports.json        WASM から公開する関数一覧
├── package.json        Node からのテスト用({"type":"module"})
├── build.ps1           ビルドスクリプト
└── vendor/             Three.js(CDN 依存を避けて同梱)
```

エンジン側のソースは `code/web/engine_api.cpp`。
探索・評価・盤面・置換表は **CLI 版と同一のヘッダをそのまま include** している。

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

## テスト

| コマンド | 内容 |
|---|---|
| `node web/test_node.mjs` | WASM の API 動作確認 + プロファイル別の速度 |
| `node web/test_worker.mjs` | Worker のメッセージプロトコル(ブラウザ不要) |
| `node web/bench_fixed.mjs` | native と同一局面での速度比較 |
| `node build/e2e/e2e.mjs` | 実ブラウザ E2E(描画・クリック着手・透視・undo・難易度) |
| `node build/e2e/e2e_endgame.mjs` | 実ブラウザ E2E(終局・勝利ライン・結果表示) |

E2E は `build/e2e` で `npm i puppeteer-core` 済みであること、
および上記のローカルサーバが 8777 で動いていることが前提。

native 側:

```
g++ -std=c++17 -O2 -DBENCH -DYON_NO_MAIN -DYON_DEPTH_TARGET=yon_depth_target \
    code/web/engine_api.cpp code/web/test_engine_api.cpp -o build/test_api.exe
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
```
