# 立体四目並べ Web 版 WASM ビルドスクリプト
#   使い方: powershell -ExecutionPolicy Bypass -File web\build.ps1 [-EmsdkDir C:\emsdk] [-NoBench]
#
# 出力: web\yonmoku.js(ES module glue) と web\yonmoku.wasm
# 生成物は Git にコミットする(Cloudflare Pages 側でビルドしないため)。
#   設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §6

param(
    [string]$EmsdkDir = "C:\emsdk",
    [switch]$NoBench                  # 指定すると -DBENCH を外す(ノード数計測を無効化)
)

$ErrorActionPreference = "Stop"
$repo = Split-Path -Parent $PSScriptRoot

# --- emsdk の場所を解決 ---
$emppPy  = Join-Path $EmsdkDir "upstream\emscripten\em++.py"
if (-not (Test-Path $emppPy)) {
    throw "em++ が見つかりません: $emppPy`n  emsdk を導入してください:`n    git clone https://github.com/emscripten-core/emsdk.git $EmsdkDir`n    $EmsdkDir\emsdk.bat install latest`n    $EmsdkDir\emsdk.bat activate latest"
}
$python = Get-ChildItem (Join-Path $EmsdkDir "python") -Directory | Select-Object -First 1
if ($null -eq $python) { throw "emsdk の python が見つかりません" }
$pythonExe = Join-Path $python.FullName "python.exe"
$env:EM_CONFIG = Join-Path $EmsdkDir ".emscripten"

# --- ビルドフラグ ---
$defines = @(
    "-DUSE_ENDGAME_R2=1",              # 最終盤の段パリティ規則 R2
    "-DUSE_ENDGAME_CUT=1",             # 最終盤のゲート付き厳密打ち切り
    "-DYON_DEPTH_TARGET=yon_depth_target"   # ★難易度プロファイルで読み深さを差し替える
)
if (-not $NoBench) { $defines += "-DBENCH" }   # 探索ノード数の計測(実測でコストは誤差範囲)

$flags = @(
    "-std=c++17", "-O3", "-msimd128",
    "-sALLOW_MEMORY_GROWTH=1", "-sINITIAL_MEMORY=128MB", "-sMAXIMUM_MEMORY=512MB",
    "-sMODULARIZE=1", "-sEXPORT_ES6=1", "-sEXPORT_NAME=YonmokuModule",
    "-sENVIRONMENT=web,worker,node",
    "-sEXPORTED_RUNTIME_METHODS=cwrap,ccall,UTF8ToString,HEAP32",
    "-sEXPORTED_FUNCTIONS=@web/exports.json"
)

$src = "code/web/engine_api.cpp"
$out = "web/yonmoku.js"

Push-Location $repo
try {
    Write-Host "building $out ..." -ForegroundColor Cyan
    & $pythonExe $emppPy @flags @defines $src -o $out
    if ($LASTEXITCODE -ne 0) { throw "em++ failed with exit code $LASTEXITCODE" }

    $wasm = Join-Path $repo "web\yonmoku.wasm"
    $js   = Join-Path $repo "web\yonmoku.js"
    Write-Host ("OK  yonmoku.wasm = {0:N0} bytes / yonmoku.js = {1:N0} bytes" -f `
        (Get-Item $wasm).Length, (Get-Item $js).Length) -ForegroundColor Green
    Write-Host "動作確認: node web\test_node.mjs" -ForegroundColor DarkGray
}
finally { Pop-Location }
