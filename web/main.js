// 立体四目並べ 3D UI(メインスレッド)。
// 探索は worker.js の中の WASM が担当し、ここは描画と入力だけを行う。
//   設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §4
//
// 座標系: 盤の (x, y, z) → world (x-1.5, z-1.5, y-1.5)   ※盤の z が高さ(重力方向)
//         マス番号 sq = x + y*4 + z*16

import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

const $ = (id) => document.getElementById(id);
const SIZE = 4;
const sqX = (sq) => sq % SIZE;
const sqY = (sq) => Math.floor(sq / SIZE) % SIZE;
const sqZ = (sq) => Math.floor(sq / (SIZE * SIZE));
const cellPos = (x, y, z) => new THREE.Vector3(x - 1.5, z - 1.5, y - 1.5);

function fatal(msg) {
  $('boot').classList.add('hidden');
  $('fatal-msg').textContent = msg;
  $('fatal').classList.remove('hidden');
}

// ===== レンダラ =====
const canvas = $('scene');
let renderer;
try {
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
} catch (e) {
  fatal('このブラウザでは WebGL が利用できないため 3D 盤面を表示できません。WebGL を有効にするか、別のブラウザでお試しください。');
  throw e;
}
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
renderer.shadowMap.enabled = true;
renderer.shadowMap.type = THREE.PCFSoftShadowMap;

// ===== シーン =====
const scene = new THREE.Scene();
scene.background = new THREE.Color(0x0e1116);

const camera = new THREE.PerspectiveCamera(34, 1, 0.1, 100);
const CAM_HOME = new THREE.Vector3(7.4, 7.2, 9.4);
camera.position.copy(CAM_HOME);

const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.dampingFactor = 0.08;
controls.minDistance = 7.0;
controls.maxDistance = 26;
controls.minPolarAngle = 0.18;
controls.maxPolarAngle = Math.PI * 0.49;   // 盤の下に潜り込ませない
controls.target.set(0, -0.25, 0);
controls.autoRotateSpeed = 0.9;

scene.add(new THREE.HemisphereLight(0x9fc4ff, 0x0b0e13, 1.05));
const key = new THREE.DirectionalLight(0xffffff, 2.0);
key.position.set(6, 10, 5);
key.castShadow = true;
key.shadow.mapSize.set(1024, 1024);
key.shadow.camera.left = -6; key.shadow.camera.right = 6;
key.shadow.camera.top = 6; key.shadow.camera.bottom = -6;
scene.add(key);
const rim = new THREE.DirectionalLight(0x6ba8ff, 0.9);   // 奥の石の輪郭を出すリムライト
rim.position.set(-7, 3, -6);
scene.add(rim);

// ===== 盤の構造 =====
const boardGroup = new THREE.Group();
scene.add(boardGroup);

const base = new THREE.Mesh(
  new THREE.BoxGeometry(4.6, 0.3, 4.6),
  new THREE.MeshStandardMaterial({ color: 0x1b2129, roughness: 0.85, metalness: 0.1 }),
);
base.position.y = -2.16;
base.receiveShadow = true;
boardGroup.add(base);

const grid = new THREE.GridHelper(4, 4, 0x3d4b5c, 0x2a333f);
grid.position.y = -2.0;
boardGroup.add(grid);

// 支柱 16 本 + 不可視の当たり判定シリンダー
const rodGeo = new THREE.CylinderGeometry(0.052, 0.052, 4.0, 12);
const rodMat = new THREE.MeshStandardMaterial({ color: 0x39434f, roughness: 0.55, metalness: 0.35 });
const rodMatHi = new THREE.MeshStandardMaterial({ color: 0x4f9dff, roughness: 0.35, metalness: 0.45, emissive: 0x1d4d8a });
const hitGeo = new THREE.CylinderGeometry(0.46, 0.46, 4.2, 10);
const hitMat = new THREE.MeshBasicMaterial({ visible: false });

const rods = [];      // [x + y*4] → rod mesh
const hitboxes = [];  // レイキャスト対象
for (let y = 0; y < SIZE; y++) {
  for (let x = 0; x < SIZE; x++) {
    const rod = new THREE.Mesh(rodGeo, rodMat);
    rod.position.set(x - 1.5, 0, y - 1.5);
    boardGroup.add(rod);
    rods[x + y * SIZE] = rod;

    const hit = new THREE.Mesh(hitGeo, hitMat);
    hit.position.set(x - 1.5, 0, y - 1.5);
    hit.userData = { x, y };
    boardGroup.add(hit);
    hitboxes.push(hit);
  }
}

// ===== 石 =====
const STONE_R = 0.38;
const stoneGeo = new THREE.SphereGeometry(STONE_R, 30, 22);
const mat = {
  black:     new THREE.MeshStandardMaterial({ color: 0x2b323b, roughness: 0.32, metalness: 0.42 }),
  white:     new THREE.MeshStandardMaterial({ color: 0xe9ecf1, roughness: 0.28, metalness: 0.12 }),
  blackXray: new THREE.MeshStandardMaterial({ color: 0x2b323b, roughness: 0.32, metalness: 0.42, transparent: true, opacity: 0.3, depthWrite: false }),
  whiteXray: new THREE.MeshStandardMaterial({ color: 0xe9ecf1, roughness: 0.28, metalness: 0.12, transparent: true, opacity: 0.3, depthWrite: false }),
  blackWin:  new THREE.MeshStandardMaterial({ color: 0x1b2733, roughness: 0.3, metalness: 0.3, emissive: 0x2f7d46 }),
  whiteWin:  new THREE.MeshStandardMaterial({ color: 0xe9ecf1, roughness: 0.25, metalness: 0.12, emissive: 0x2f7d46 }),
};

const stones = new Map();   // sq → mesh
const stoneGroup = new THREE.Group();
scene.add(stoneGroup);

// ゴースト石(落下先のプレビュー)
const ghost = new THREE.Mesh(stoneGeo, new THREE.MeshStandardMaterial({
  color: 0x4f9dff, transparent: true, opacity: 0.34, depthWrite: false,
}));
ghost.visible = false;
scene.add(ghost);

// 直前手のリング
const ring = new THREE.Mesh(
  new THREE.TorusGeometry(STONE_R + 0.1, 0.032, 10, 40),
  new THREE.MeshBasicMaterial({ color: 0x4f9dff, transparent: true, opacity: 0.95 }),
);
ring.rotation.x = Math.PI / 2;
ring.visible = false;
scene.add(ring);

// 研究モードの候補手リング(1 位 = 金 / 2 位 = 銀 / 3 位 = 銅。候補手カードの色と対応)
const CAND_COLORS = [0xe8c25a, 0xb9c3cf, 0xc98a55, 0x6c7684, 0x6c7684];
const candRings = CAND_COLORS.map((c, i) => {
  const m = new THREE.Mesh(
    new THREE.TorusGeometry(STONE_R + 0.16 - i * 0.012, 0.026, 10, 40),
    new THREE.MeshBasicMaterial({ color: c, transparent: true, opacity: 0.9 }),
  );
  m.rotation.x = Math.PI / 2;
  m.visible = false;
  scene.add(m);
  return m;
});

// ===== 状態 =====
let S = null;              // worker から届いた最新の state
let profiles = [];
let models = [];
let limits = { maxRows: 8, maxPly: 30, minPly: 2 };
let busy = true;           // AI 思考中 or 起動中
let hoverCol = -1;         // ホバー中の列 index(x + y*4)
let keyCol = 5;            // キーボード選択中の列
let thinkStart = 0;
const anims = [];          // 落下アニメーション

// ===== 研究モード =====
// 対局モードとの違いは「AI が自動で指さない」「両色を自分で置ける」「1 手ずつ戻す」の 3 点。
//   設計: docs/設計書/Web公開/implementation-plan-research-analysis.md
const SOLVED = 1e8;        // |評価値| がこれ以上なら勝敗を読み切っている
let research = false;      // 研究モードか
let analyzing = false;     // 解析ループが走っているか
let anaRows = [];          // 深化の推移(新しい順)
let anaCands = [];         // 最新反復の候補手
let anaStartedAt = 0;

// ===== Worker =====
const worker = new Worker(new URL('./worker.js', import.meta.url), { type: 'module' });
worker.onerror = (e) => fatal('エンジンの読み込みに失敗しました: ' + (e.message || e.filename || 'unknown error'));
worker.onmessage = (e) => handle(e.data);
worker.postMessage({ type: 'init' });

function handle(m) {
  switch (m.type) {
    case 'ready':
      profiles = m.profiles;
      models = m.models;
      limits = m.limits;
      buildModelSelect(m.defaultModel);
      buildProfileSelect(m.defaultProfile);
      buildAnalyzeSelects();
      restoreSettings(m.defaultProfile, m.defaultModel);
      $('boot').classList.add('hidden');
      busy = false;
      newGame();
      break;
    case 'schedule':
      if (!m.ok) $('schedwarn').textContent = scheduleError(m.code);
      break;
    case 'model':
      if (!m.ok) $('schedwarn').textContent = 'このモデルは読み込めませんでした。';
      break;
    case 'thinking':
      busy = true;
      thinkStart = performance.now();
      $('thinking').classList.remove('hidden');
      if ($('spin').checked) controls.autoRotate = true;
      break;
    case 'moved':
      controls.autoRotate = false;
      $('thinking').classList.add('hidden');
      break;
    case 'state':
      applyState(m);
      break;
    case 'played':
      break;
    case 'analyzeIter':
      onAnalyzeIter(m);
      break;
    case 'analyzeEnd':
      onAnalyzeEnd(m.reason);
      break;
    case 'error':
      fatal('エンジンでエラーが発生しました: ' + m.message);
      break;
    default:
      break;
  }
}

// ===== モデルセレクト =====
// 1 モデル = (探索エンジン, 重みバージョン)。エンジンごとに optgroup へまとめる。
function buildModelSelect(def) {
  const sel = $('model');
  sel.innerHTML = '';
  const groups = new Map();
  for (const m of models) {
    if (!groups.has(m.name)) {
      const g = document.createElement('optgroup');
      g.label = m.name;
      groups.set(m.name, g);
      sel.appendChild(g);
    }
    const o = document.createElement('option');
    o.value = String(m.id);
    o.textContent = `${m.name} — ${m.weights || '未読込'}`;
    o.disabled = !m.available;
    groups.get(m.name).appendChild(o);
  }
  sel.value = String(def);
}

// 選択中のモデルが core エンジンか(重い設定の警告しきい値に使う)
const isCoreModel = () => (models.find((m) => m.id === Number($('model').value)) || {}).name === 'core';

// ===== 難易度セレクト(プリセット + カスタム) =====
const CUSTOM = -1;

function buildProfileSelect(def) {
  const sel = $('profile');
  sel.innerHTML = '';
  for (const p of profiles) {
    const o = document.createElement('option');
    // 読み手数を実数値で併記する(設計書 M4)
    o.value = String(p.id);
    o.textContent = `${p.name} — ${p.plies.join('/')}手読み`;
    sel.appendChild(o);
  }
  const c = document.createElement('option');
  c.value = String(CUSTOM);
  c.textContent = 'カスタム';
  sel.appendChild(c);
  sel.value = String(def);
  buildScheduleTable(profiles[def].rows);
  updateProfileHint();
}

function updateProfileHint() {
  const rows = readScheduleTable();
  const detail = rows.map(([t, n]) => `${t}手目〜${n}`).join(' / ') + ' 手読み';
  const heavy = heavyRows(rows).length > 0;
  $('profile').title = detail + (heavy ? '\n※ 1手に数十秒〜数分かかることがあります' : '');
  $('profilehint').textContent = detail;
}

// ===== 読み手数スケジュール =====
// 行は [手数, 読み手数]。手数はエンジンの turn(= 石数 + 1 = 「何手目を指すか」)。

const plyOptions = () => {
  const out = [];
  for (let n = limits.minPly; n <= limits.maxPly; n += 2) out.push(n);
  return out;
};

function buildScheduleTable(rows) {
  const tbl = $('schedtable');
  tbl.innerHTML = '';
  rows.forEach(([turn, ply], i) => {
    const tr = document.createElement('tr');
    if (i === 0) tr.className = 'fixed';   // 先頭行の手数は 1 固定

    const tdTurn = document.createElement('td');
    const selTurn = document.createElement('select');
    selTurn.className = 'turn';
    for (let t = 1; t <= 64; t++) {
      const o = document.createElement('option');
      o.value = String(t);
      o.textContent = String(t);
      selTurn.appendChild(o);
    }
    selTurn.value = String(i === 0 ? 1 : turn);
    selTurn.disabled = (i === 0);
    selTurn.addEventListener('change', onScheduleEdited);
    tdTurn.appendChild(selTurn);

    const tdUnit = document.createElement('td');
    tdUnit.className = 'unit';
    tdUnit.textContent = '手目以降';

    const tdPly = document.createElement('td');
    const selPly = document.createElement('select');
    selPly.className = 'ply';
    for (const n of plyOptions()) {
      const o = document.createElement('option');
      o.value = String(n);
      o.textContent = String(n);
      selPly.appendChild(o);
    }
    selPly.value = String(ply);
    selPly.addEventListener('change', onScheduleEdited);
    tdPly.appendChild(selPly);

    const tdUnit2 = document.createElement('td');
    tdUnit2.className = 'unit';
    tdUnit2.textContent = '手読み';

    const tdDel = document.createElement('td');
    tdDel.className = 'del';
    if (i > 0) {
      const b = document.createElement('button');
      b.className = 'rowdel';
      b.textContent = '×';
      b.title = 'この行を削除';
      b.addEventListener('click', () => { tr.remove(); onScheduleEdited(); });
      tdDel.appendChild(b);
    }

    tr.append(tdTurn, tdUnit, tdPly, tdUnit2, tdDel);
    tbl.appendChild(tr);
  });
  updateScheduleWarn();
}

function readScheduleTable() {
  return [...$('schedtable').querySelectorAll('tr')].map((tr) => [
    Number(tr.querySelector('.turn').value),
    Number(tr.querySelector('.ply').value),
  ]);
}

// エンジン側 yon_set_schedule と同じ規則で検証する(送る前に UI で弾く)
function validateSchedule(rows) {
  if (rows.length < 1 || rows.length > limits.maxRows) return `行は 1〜${limits.maxRows} 行にしてください。`;
  if (rows[0][0] !== 1) return '1 行目は「1 手目以降」にしてください。';
  for (let i = 0; i < rows.length; i++) {
    const [t, n] = rows[i];
    if (t < 1 || t > 64) return '手数は 1〜64 の範囲です。';
    if (i > 0 && t <= rows[i - 1][0]) return '手数は上から順に大きくしてください(同じ手数は不可)。';
    if (n % 2 !== 0) return '読み手数は偶数のみです(評価関数が偶数手読みを前提にしているため)。';
    if (n < limits.minPly || n > limits.maxPly) return `読み手数は ${limits.minPly}〜${limits.maxPly} です。`;
  }
  return '';
}

function scheduleError(code) {
  switch (code) {
    case -1: return `行は 1〜${limits.maxRows} 行にしてください。`;
    case -2: return '1 行目は「1 手目以降」にしてください。';
    case -3: return '手数は上から順に大きくしてください。';
    case -4: return `読み手数は ${limits.minPly}〜${limits.maxPly} の偶数です。`;
    default: return '読み手数の設定を受け付けられませんでした。';
  }
}

// 中止ボタンが無いので、返ってこなくなる設定は事前に警告する。
// core は同じ読み手数でも alpha の 3〜4 倍のノードを探索する(実測: 標準で 35M → 124M ノード。
// docs/実行結果/benchmark-results-web-model-select.md)ので、しきい値を 1 段下げる。
function heavyRows(rows) {
  const limit = isCoreModel() ? 12 : 16;
  return rows.filter(([t, n]) => t <= 20 && n >= limit);
}

function updateScheduleWarn() {
  const rows = readScheduleTable();
  const err = validateSchedule(rows);
  const el = $('schedwarn');
  if (err) { el.textContent = err; el.className = 'note err'; return; }
  const heavy = heavyRows(rows);
  if (heavy.length) {
    el.textContent = `${heavy[0][0]} 手目から ${heavy[0][1]} 手読みは 1 手に数十秒〜数分かかることがあります。`
                   + 'その間ページは操作できません。';
    el.className = 'note warn';
  } else {
    el.textContent = '';
    el.className = 'note';
  }
}

function onScheduleEdited() {
  $('profile').value = String(CUSTOM);   // 表を触ったらカスタム扱い
  updateScheduleWarn();
  updateProfileHint();
  sendSchedule();
}

function sendSchedule() {
  const rows = readScheduleTable();
  if (validateSchedule(rows)) return false;   // NG なら送らない(警告は updateScheduleWarn が出している)
  saveSettings();
  worker.postMessage({ type: 'setSchedule', rows });
  return true;
}

// ===== 設定の保存・復元 =====
const STORE_KEY = 'yonmoku.settings.v1';

function saveSettings() {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify({
      model: Number($('model').value),
      profile: Number($('profile').value),
      rows: readScheduleTable(),
      research,
      ana: {
        start: Number($('ana-start').value),
        topK: Number($('ana-topk').value),
        limit: Number($('ana-limit').value),
        fresh: $('ana-fresh').checked,
      },
    }));
  } catch (e) { /* プライベートモード等では黙って諦める */ }
}

function restoreSettings(def, defModel) {
  let s = null;
  try { s = JSON.parse(localStorage.getItem(STORE_KEY) || 'null'); } catch (e) { s = null; }
  if (!s || !Array.isArray(s.rows) || validateSchedule(s.rows)) {
    // 保存が無い / 壊れている / 規則違反 → 既定プリセットに戻す
    $('profile').value = String(def);
    buildScheduleTable(profiles[def].rows);
    updateProfileHint();
    restoreAnalyzeSettings(s);
    return;
  }
  const m = models.find((x) => x.id === s.model && x.available);
  $('model').value = String(m ? m.id : defModel);
  if (m && m.id !== defModel) worker.postMessage({ type: 'setModel', model: m.id });
  $('profile').value = String(s.profile === CUSTOM ? CUSTOM : s.profile);
  buildScheduleTable(s.rows);
  updateProfileHint();
  worker.postMessage({ type: 'setSchedule', rows: s.rows });
  restoreAnalyzeSettings(s);
}

// 研究モードの設定を復元する(解析そのものは復元しない)
function restoreAnalyzeSettings(s) {
  const a = s && s.ana;
  if (a) {
    if (a.start) $('ana-start').value = String(a.start);
    if (a.topK) $('ana-topk').value = String(a.topK);
    if (typeof a.limit === 'number') $('ana-limit').value = String(a.limit);
    $('ana-fresh').checked = !!a.fresh;
  }
  if (s && s.research) setResearch(true);
}

// ===== 状態の反映 =====
function applyState(s) {
  const prev = S;
  S = s;

  syncStones(prev);
  updateRing();
  updateHUD();

  if (research) {
    // 研究モードは両色を人が置く。AI の自動思考も結果モーダルも出さない
    busy = analyzing;
    refreshButtons();
    return;
  }

  const humanTurn = (s.status === 0) && (s.blackToMove === s.humanIsBlack);
  if (s.status !== 0) {
    busy = false;
    showResult();
  } else if (!humanTurn) {
    // AI の手番 → 少し置いてから思考させる(落下アニメの視認性のため)
    busy = true;
    setTimeout(() => worker.postMessage({ type: 'think' }), 260);
  } else {
    busy = false;
  }
  refreshButtons();
}

function syncStones(prev) {
  const want = new Map();
  for (const sq of S.black) want.set(sq, 'black');
  for (const sq of S.white) want.set(sq, 'white');
  const winSet = new Set(S.winLine);

  // 消えた石(undo / 新規対局)を取り除く
  for (const [sq, mesh] of stones) {
    if (!want.has(sq)) { stoneGroup.remove(mesh); stones.delete(sq); }
  }
  // 増えた石を追加(新規は落下アニメーション)
  for (const [sq, color] of want) {
    if (stones.has(sq)) continue;
    const mesh = new THREE.Mesh(stoneGeo, mat[color]);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    const target = cellPos(sqX(sq), sqY(sq), sqZ(sq));
    mesh.position.copy(target);
    mesh.userData = { sq, color };
    stoneGroup.add(mesh);
    stones.set(sq, mesh);
    if (prev) {   // 初期化直後(棋譜の一括再生)ではアニメーションしない
      mesh.position.y = 2.9;
      anims.push({ mesh, from: 2.9, to: target.y, t: 0, dur: 300 });
    }
  }
  applyStoneMaterials(winSet);
}

function applyStoneMaterials(winSet) {
  const xray = $('xray').checked;
  for (const [sq, mesh] of stones) {
    const color = mesh.userData.color;
    if (winSet.has(sq)) {
      mesh.material = color === 'black' ? mat.blackWin : mat.whiteWin;
    } else if (xray && sq !== S.lastSq) {
      // 透視中も直前手だけは不透明にして位置を見失わないようにする
      mesh.material = color === 'black' ? mat.blackXray : mat.whiteXray;
    } else {
      mesh.material = color === 'black' ? mat.black : mat.white;
    }
  }
}

function updateRing() {
  if (S.lastSq < 0) { ring.visible = false; return; }
  const p = cellPos(sqX(S.lastSq), sqY(S.lastSq), sqZ(S.lastSq));
  ring.position.copy(p);
  ring.visible = true;
}

// ===== HUD =====
function updateHUD() {
  $('movecount').textContent = String(S.moveCount);

  // いま効いている読み手数。UI の「手数」は石数、スケジュールの「n 手目」は石数 + 1
  $('schedhint').textContent = S.status === 0 ? `次は ${S.turn} 手目 / ${S.currentPly} 手読み` : '';

  const who = S.blackToMove ? '黒' : '白';
  const isHuman = research || S.blackToMove === S.humanIsBlack;   // 研究モードは両色とも人が置く
  $('turnwho').textContent = S.status === 0 ? `${who}(${isHuman ? 'あなた' : 'AI'})` : '—';

  // 評価値(常に黒視点。設計書 §4.6.1)。画面上部の HUD に大きく出す
  const card = $('evalcard');
  const hud = $('evalhud');
  if (!S.evalValid) {
    $('score').textContent = '—';
    $('score').style.color = '';
    $('wr-black').textContent = '黒 50.0%';
    $('wr-white').textContent = '50.0% 白';
    $('winbar-black').style.width = '50%';
    $('thinktime').textContent = '—';
    $('nodes').textContent = '—';
    $('evalfresh').textContent = '';
    $('evalfresh').className = 'tag';
    hud.classList.remove('stale');
    card.classList.remove('stale');
    $('evalnote').textContent = research
      ? '「解析開始」を押すと、8 手読みから 2 手ずつ深めていきます。'
      : 'AI が最初の手を考えると評価値が表示されます。';
  } else {
    const wr = Math.max(0, Math.min(100, S.winRateBlack));
    $('winbar-black').style.width = wr.toFixed(1) + '%';
    $('wr-black').textContent = `黒 ${wr.toFixed(1)}%`;
    $('wr-white').textContent = `${(100 - wr).toFixed(1)}% 白`;
    // 読み切ると評価値は ±1e9 付近になるので、そのまま数字にせず「勝ち確定」と出す
    $('score').textContent = S.isMate
      ? (S.scoreBlack > 0 ? '黒 勝ち確定' : '白 勝ち確定')
      : scoreLabel(S.scoreBlack).replace('必勝', '勝ち確定');
    // 優勢な側の色を数字にも乗せる(将棋中継の評価値表示と同じ読み方ができるように)
    $('score').style.color = S.scoreBlack === 0 ? '' : (S.scoreBlack > 0 ? 'var(--fg)' : 'var(--accent)');
    $('thinktime').textContent = (S.lastMs / 1000).toFixed(2) + ' 秒';
    $('nodes').textContent = S.lastNodes >= 0 ? Math.round(S.lastNodes).toLocaleString() : '—';

    if (research) {
      // 研究モードでは「何手読みの値か」を出す。解析していない局面では古い値になる
      const stale = analyzing ? false : S.anaPly === 0;
      hud.classList.toggle('stale', stale);
      card.classList.toggle('stale', stale);
      $('evalfresh').textContent = S.anaPly > 0 ? `${S.anaPly} 手読み` : '未解析';
      $('evalfresh').className = stale ? 'tag stale' : 'tag';
      $('evalnote').textContent = S.anaPly > 0
        ? 'この局面を ' + S.anaPly + ' 手読みで解析した結果です。'
        : '「解析開始」を押すと、8 手読みから 2 手ずつ深めていきます。';
    } else {
      // 人間の手番中は「AI が前回思考した時点の値」なので、古いことを明示する
      const stale = S.status === 0 && isHuman;
      hud.classList.toggle('stale', stale);
      card.classList.toggle('stale', stale);
      $('evalfresh').textContent = stale ? 'AI 前回思考時点' : '最新';
      $('evalfresh').className = stale ? 'tag stale' : 'tag';
      $('evalnote').textContent = stale
        ? 'あなたの手番中は、AI が直前に読んだ時点の評価値を表示しています。'
        : '';
    }
  }

  // 棋譜
  const ol = $('record');
  ol.innerHTML = '';
  S.hand.forEach(([x, y], i) => {
    const li = document.createElement('li');
    li.className = i % 2 === 0 ? 'black' : 'white';
    li.innerHTML = `<b>${i % 2 === 0 ? '●' : '○'}</b> (${x + 1}, ${y + 1})`;
    ol.appendChild(li);
  });
  ol.scrollTop = ol.scrollHeight;

  // 結果行
  const sl = $('statusline');
  sl.className = 'status';
  if (S.status === 0) {
    sl.textContent = '';
  } else if (S.status === 3) {
    sl.textContent = '引き分け';
  } else {
    const humanWon = (S.status === 1) === S.humanIsBlack;
    sl.textContent = (S.status === 1 ? '黒の勝ち' : '白の勝ち') + (humanWon ? '(あなたの勝ち)' : '(AI の勝ち)');
    sl.classList.add(humanWon ? 'win' : 'lose');
  }
}

function showResult() {
  if (S.status === 0) return;
  const humanWon = (S.status === 1) === S.humanIsBlack;
  $('result-title').textContent = S.status === 3 ? '引き分け' : (humanWon ? 'あなたの勝ち' : 'AI の勝ち');
  $('result-sub').textContent = `${S.moveCount} 手 / ${S.status === 3 ? '盤面が埋まりました' : (S.status === 1 ? '黒' : '白') + 'が四目を並べました'}`;
  $('result').classList.remove('hidden');
}

function refreshButtons() {
  const canPlace = S && S.status === 0 && (research || S.blackToMove === S.humanIsBlack);
  $('undo').disabled = busy || !S || S.moveCount === 0;
  $('profile').disabled = busy || research;   // 研究モードは N を直接指定するので使わない
  $('model').disabled = busy;
  $('side').disabled = busy;
  $('research').disabled = busy;
  $('schedcard').classList.toggle('busy', busy);   // 思考中はスケジュールを触らせない

  // ★停止ボタンだけは解析中でも押せるようにする(押しても止まるのは反復の合間)
  $('anacard').classList.toggle('busy', analyzing);
  $('ana-run').disabled = analyzing || !S || S.status !== 0;
  $('ana-stop').disabled = !analyzing;

  canvas.style.cursor = canPlace && !busy ? (hoverCol >= 0 ? 'pointer' : 'grab') : 'default';
}

// ===== 入力 =====
const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();
let pointerInside = false;

function updatePointer(ev) {
  const r = canvas.getBoundingClientRect();
  pointer.x = ((ev.clientX - r.left) / r.width) * 2 - 1;
  pointer.y = -((ev.clientY - r.top) / r.height) * 2 + 1;
  pointerInside = true;
}

function pickColumn() {
  if (!S || S.status !== 0 || busy) return -1;
  if (!research && S.blackToMove !== S.humanIsBlack) return -1;   // 研究モードは両色とも人が置く
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObjects(hitboxes, false);
  for (const h of hits) {
    const { x, y } = h.object.userData;
    const col = x + y * SIZE;
    if (S.landing[col] >= 0) return col;   // 満杯の列は選べない
  }
  return -1;
}

function setHover(col) {
  if (col === hoverCol) return;
  if (hoverCol >= 0) rods[hoverCol].material = rodMat;
  hoverCol = col;
  if (hoverCol >= 0) {
    rods[hoverCol].material = rodMatHi;
    const x = hoverCol % SIZE, y = Math.floor(hoverCol / SIZE);
    const z = S.landing[hoverCol];
    ghost.position.copy(cellPos(x, y, z));
    ghost.material.color.set((research ? S.blackToMove : S.humanIsBlack) ? 0x5a6472 : 0xdfe4ea);
    ghost.visible = true;
  } else {
    ghost.visible = false;
  }
  refreshButtons();
}

function playColumn(col) {
  if (col < 0 || !S || busy) return;
  if (S.status !== 0) return;
  if (!research && S.blackToMove !== S.humanIsBlack) return;
  if (S.landing[col] < 0) return;
  busy = true;
  setHover(-1);
  if (research) clearAnalysis();   // 局面が変わったら前の解析結果は捨てる
  worker.postMessage({ type: 'play', x: col % SIZE, y: Math.floor(col / SIZE) });
}

canvas.addEventListener('pointermove', (ev) => { updatePointer(ev); });
canvas.addEventListener('pointerleave', () => { pointerInside = false; setHover(-1); });

// ドラッグ(視点回転)とクリック(着手)を区別する
let downAt = null;
canvas.addEventListener('pointerdown', (ev) => { downAt = { x: ev.clientX, y: ev.clientY, t: performance.now() }; });
canvas.addEventListener('pointerup', (ev) => {
  if (!downAt) return;
  const moved = Math.hypot(ev.clientX - downAt.x, ev.clientY - downAt.y);
  const quick = performance.now() - downAt.t < 600;
  downAt = null;
  if (moved > 6 || !quick) return;   // 回転操作とみなす
  updatePointer(ev);
  playColumn(pickColumn());
});

// キーボード操作
addEventListener('keydown', (ev) => {
  if (!S || busy) return;
  let x = keyCol % SIZE, y = Math.floor(keyCol / SIZE);
  switch (ev.key) {
    case 'ArrowLeft':  x = (x + SIZE - 1) % SIZE; break;
    case 'ArrowRight': x = (x + 1) % SIZE; break;
    case 'ArrowUp':    y = (y + SIZE - 1) % SIZE; break;
    case 'ArrowDown':  y = (y + 1) % SIZE; break;
    case 'Enter': case ' ':
      ev.preventDefault();
      playColumn(keyCol);
      return;
    default: return;
  }
  ev.preventDefault();
  keyCol = x + y * SIZE;
  setHover(S.landing[keyCol] >= 0 ? keyCol : -1);
});

// ===== HUD 操作 =====
function newGame() {
  $('result').classList.add('hidden');
  busy = true;
  // 石をすべて消してから再構築する(アニメーションを走らせない)
  for (const [, mesh] of stones) stoneGroup.remove(mesh);
  stones.clear();
  S = null;
  worker.postMessage({
    type: 'newGame',
    humanIsBlack: $('side').value === 'black',
    profile: Number($('profile').value),
  });
}

$('newgame').addEventListener('click', newGame);
$('result-again').addEventListener('click', newGame);
$('result-close').addEventListener('click', () => $('result').classList.add('hidden'));
$('undo').addEventListener('click', () => {
  if (busy || !S || S.moveCount === 0) return;
  busy = true;
  $('result').classList.add('hidden');
  // ★既存の undo は「AI 手 + 人間手」の 2 手戻し。研究モードでは 1 手ずつ戻す
  worker.postMessage({ type: research ? 'undoOne' : 'undo' });
  if (research) clearAnalysis();
});
$('profile').addEventListener('change', () => {
  const id = Number($('profile').value);
  if (id !== CUSTOM) {
    buildScheduleTable(profiles[id].rows);   // プリセットを表へ流し込む
    updateProfileHint();
    saveSettings();
    if (S) worker.postMessage({ type: 'setProfile', profile: id });
  } else {
    updateProfileHint();
    saveSettings();
  }
});
$('model').addEventListener('change', () => {
  saveSettings();
  updateScheduleWarn();   // core は同じ読み手数でも重いので警告のしきい値が変わる
  worker.postMessage({ type: 'setModel', model: Number($('model').value) });
});
$('sched-add').addEventListener('click', () => {
  const rows = readScheduleTable();
  if (rows.length >= limits.maxRows) {
    $('schedwarn').textContent = `行は最大 ${limits.maxRows} 行です。`;
    $('schedwarn').className = 'note err';
    return;
  }
  const last = rows[rows.length - 1];
  rows.push([Math.min(64, last[0] + 8), last[1]]);   // 直前の行の 8 手あと・同じ読み手数で追加
  buildScheduleTable(rows);
  onScheduleEdited();
});
$('sched-reset').addEventListener('click', () => {
  const id = Number($('profile').value);
  const p = profiles[id === CUSTOM ? (profiles.find((x) => x.id === 3) ? 3 : 0) : id];
  $('profile').value = String(p.id);
  buildScheduleTable(p.rows);
  updateProfileHint();
  saveSettings();
  worker.postMessage({ type: 'setProfile', profile: p.id });
});
$('side').addEventListener('change', newGame);
$('xray').addEventListener('change', () => { if (S) applyStoneMaterials(new Set(S.winLine)); });
$('spin').addEventListener('change', () => { if (!$('spin').checked) controls.autoRotate = false; });
$('resetcam').addEventListener('click', () => {
  camera.position.copy(CAM_HOME);
  controls.target.set(0, -0.25, 0);
  controls.update();
});

// E2E テスト用フック。?e2e=1 を付けたときだけ生える(通常の利用では何も公開しない)。
// 3D のクリック座標を計算せずに列を指定して着手できるようにするためだけのもの。
if (new URLSearchParams(location.search).has('e2e')) {
  window.__yonE2E = {
    play: (col) => playColumn(col),
    state: () => S,
    isBusy: () => busy,
    stoneMaterial: (sq) => (stones.get(sq)?.material === mat.blackWin || stones.get(sq)?.material === mat.whiteWin) ? 'win' : 'normal',
    // --- 研究モード ---
    research: (on) => setResearch(!!on),
    isResearch: () => research,
    analyze: (opts) => {
      if (opts) {
        if (opts.start) $('ana-start').value = String(opts.start);
        if (opts.topK) $('ana-topk').value = String(opts.topK);
        if (typeof opts.limit === 'number') $('ana-limit').value = String(opts.limit);
        if (typeof opts.fresh === 'boolean') $('ana-fresh').checked = opts.fresh;
      }
      startAnalysis();
    },
    stopAnalyze: () => $('ana-stop').click(),
    isAnalyzing: () => analyzing,
    anaRows: () => anaRows.slice(),
    cands: () => anaCands.slice(),
  };
}


// ===== 研究モード =====
// 反復深化は Worker 側の外側ループが回す(1 反復 = 1 タスク)。ここは表示と操作だけ。
//   設計: docs/設計書/Web公開/implementation-plan-research-analysis.md §5

const ANA_LIMITS = [
  [600000, '10 分'],       // 既定
  [60000, '1 分'],
  [180000, '3 分'],
  [1800000, '30 分'],
  [0, '無制限'],
];
const ANA_LIMIT_DEFAULT = 600000;

function buildAnalyzeSelects() {
  const start = $('ana-start');
  start.innerHTML = '';
  for (let n = 4; n <= 20; n += 2) {
    const o = document.createElement('option');
    o.value = String(n);
    o.textContent = `${n} 手読み`;
    start.appendChild(o);
  }
  start.value = '8';

  const k = $('ana-topk');
  k.innerHTML = '';
  for (let i = 1; i <= (limits.anaMaxK || 5); i++) {
    const o = document.createElement('option');
    o.value = String(i);
    o.textContent = `上位 ${i} 手`;
    k.appendChild(o);
  }
  k.value = String(Math.min(3, limits.anaMaxK || 3));

  const lim = $('ana-limit');
  lim.innerHTML = '';
  for (const [ms, label] of ANA_LIMITS) {
    const o = document.createElement('option');
    o.value = String(ms);
    o.textContent = label;
    lim.appendChild(o);
  }
  lim.value = String(ANA_LIMIT_DEFAULT);
}

const moveLabel = (sq) => (sq < 0 ? '—' : `(${sqX(sq) + 1}, ${sqY(sq) + 1}) ${sqZ(sq) + 1}段`);

// 評価値の表示。読み切ると生値は ±1e9 付近になるので、数字ではなく「必勝」と出す。
function scoreLabel(score) {
  if (Math.abs(score) >= SOLVED) return score > 0 ? '黒 必勝' : '白 必勝';
  if (score === 0) return '互角 0';
  return score > 0 ? `黒 +${score}` : `白 +${-score}`;
}

function clearAnalysis() {
  anaRows = [];
  anaCands = [];
  renderCandidates();
  renderAnaTable();
  $('anastate').textContent = '';
  $('candply').textContent = '';
  $('candnote').textContent = '';
  $('anawarn').textContent = '';
  $('anawarn').className = 'note';
}

function renderCandidates() {
  const ol = $('candlist');
  ol.innerHTML = '';
  for (let i = 0; i < anaCands.length; i++) {
    const c = anaCands[i];
    const li = document.createElement('li');
    li.innerHTML =
      `<span class="rank">${i + 1}</span>` +
      `<span class="mv">${moveLabel(c.sq)}</span>` +
      `<span class="sc">${scoreLabel(c.scoreBlack)}</span>` +
      `<span class="wr">${c.winRateBlack.toFixed(1)}%</span>`;
    ol.appendChild(li);
  }
  updateCandRings();
}

// 候補手の着地点にリングを出す。盤を見たまま順位が分かるようにする。
function updateCandRings() {
  for (let i = 0; i < candRings.length; i++) {
    const c = research ? anaCands[i] : null;
    if (!c || c.sq < 0) { candRings[i].visible = false; continue; }
    candRings[i].position.copy(cellPos(sqX(c.sq), sqY(c.sq), sqZ(c.sq)));
    candRings[i].visible = true;
  }
}

function renderAnaTable() {
  const t = $('anatable');
  t.innerHTML = '';
  if (anaRows.length === 0) return;
  const head = document.createElement('tr');
  head.innerHTML = '<th>読み</th><th>評価値</th><th>黒勝率</th><th>最善手</th><th>時間</th><th>ノード</th>';
  t.appendChild(head);
  anaRows.forEach((r, i) => {
    const tr = document.createElement('tr');
    if (i === 0) tr.className = 'latest';
    if (!r.complete) tr.classList.add('partial');
    // 前の反復(配列の 1 つ後ろ)から符号が反転したら色を変える
    const prev = anaRows[i + 1];
    const flip = prev && r.score !== 0 && prev.score !== 0 && Math.sign(prev.score) !== Math.sign(r.score);
    tr.innerHTML =
      `<td>${r.ply}</td>` +
      `<td class="${flip ? 'flip' : ''}">${scoreLabel(r.score)}</td>` +
      `<td>${r.winRate.toFixed(1)}%</td>` +
      `<td>${moveLabel(r.sq)}</td>` +
      `<td>${(r.ms / 1000).toFixed(2)}s</td>` +
      `<td>${r.nodes >= 0 ? Math.round(r.nodes).toLocaleString() : '—'}</td>`;
    t.appendChild(tr);
  });
}

function onAnalyzeIter(m) {
  anaCands = m.moves;
  const best = m.moves[0];
  anaRows.unshift({
    ply: m.ply,
    complete: m.complete,
    score: best ? best.scoreBlack : 0,
    winRate: best ? best.winRateBlack : 50,
    sq: best ? best.sq : -1,
    ms: m.ms,
    nodes: m.nodes,
  });
  if (anaRows.length > 40) anaRows.length = 40;

  renderCandidates();
  renderAnaTable();
  $('candply').textContent = `${m.ply} 手読み` + (m.complete ? '' : '(途中)');
  $('anastate').textContent = `${m.ply} 手読み`;

  // 候補が絞られている場合と同値切り捨てがある場合は必ず明記する(設計書 §5.4)
  const notes = [];
  if (m.forced === 1) notes.push('この局面は即勝ちがあるため、探索せずに勝ち手を返しています。');
  if (m.forced === 2) notes.push(`相手にリーチがあるため、候補は阻止手 ${m.rootMoves} 手のみです。`);
  if (m.tied > 0) notes.push(`最下位と同値の可能性がある手が他に ${m.tied} 手あります。`);
  if (!m.complete) notes.push('上限時間に達したため、この深さは途中までの結果です。');
  $('candnote').textContent = notes.join(' ');
}

function onAnalyzeEnd(reason) {
  analyzing = false;
  busy = false;
  $('thinking').classList.add('hidden');
  controls.autoRotate = false;

  const el = ((performance.now() - anaStartedAt) / 1000).toFixed(1);
  const msg = {
    stopped: '停止しました。',
    exhausted: '全読みに到達しました。これ以上深めても結果は変わりません。',
    solved: '勝敗を読み切りました。これ以上深めても結果は変わりません。',
    deadline: '1 反復の上限時間に達したので止めました。上限を延ばすと続きを読めます。',
    invalid: 'この局面は解析できません(終局しているか、打てる手がありません)。',
  }[reason] || '終了しました。';
  $('anastate').textContent = reason === 'stopped' ? '停止' : '完了';
  $('anawarn').textContent = `${msg}(経過 ${el} 秒)`;
  $('anawarn').className = (reason === 'invalid' || reason === 'deadline') ? 'note warn' : 'note';
  refreshButtons();
}

function startAnalysis() {
  if (analyzing || !S || S.status !== 0) return;
  clearAnalysis();
  analyzing = true;
  busy = true;
  anaStartedAt = performance.now();
  thinkStart = anaStartedAt;
  $('anastate').textContent = '解析中';
  $('thinking').classList.remove('hidden');
  if ($('spin').checked) controls.autoRotate = true;
  saveSettings();
  worker.postMessage({
    type: 'analyzeStart',
    startPly: Number($('ana-start').value),
    topK: Number($('ana-topk').value),
    freshTt: $('ana-fresh').checked,
    deadlineMs: Number($('ana-limit').value),
    seed: 12345,
  });
  refreshButtons();
}

function setResearch(on) {
  // 対局モードへ戻すとき、AI の手番ならそのまま指し始めてしまうので確認する
  if (!on && research && S && S.status === 0 && S.blackToMove !== S.humanIsBlack) {
    if (!confirm('対局モードに戻ると、AI の手番なのでそのまま AI が思考を始めます。よろしいですか?')) {
      $('research').checked = true;
      return;
    }
  }
  research = on;
  $('research').checked = on;
  $('anacard').classList.toggle('hidden', !on);
  $('candcard').classList.toggle('hidden', !on);
  $('anahistcard').classList.toggle('hidden', !on);
  $('schedcard').classList.toggle('hidden', on);   // 解析は N を直接指定するので使わない
  $('profile').disabled = on;
  $('profilehint').style.display = on ? 'none' : '';
  $('undo').textContent = on ? '一手戻す' : '一手戻る';
  clearAnalysis();
  updateCandRings();
  saveSettings();
  if (S) applyState(S);   // 自動思考の有無を切り替え直す
}

$('research').addEventListener('change', () => setResearch($('research').checked));
$('ana-run').addEventListener('click', startAnalysis);
$('ana-stop').addEventListener('click', () => {
  if (!analyzing) return;
  $('anastate').textContent = '停止待ち';
  // ★探索中の反復は止められない。押した瞬間に止まらない理由をここで説明しておく
  $('anawarn').textContent = '走っている反復が終わったところで止まります。';
  $('anawarn').className = 'note warn';
  worker.postMessage({ type: 'analyzeStop' });
});
for (const id of ['ana-start', 'ana-topk', 'ana-limit', 'ana-fresh']) {
  $(id).addEventListener('change', saveSettings);
}

// ===== リサイズ =====
function resize() {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  if (canvas.width === w && canvas.height === h) return;
  renderer.setSize(w, h, false);
  camera.aspect = w / Math.max(h, 1);
  camera.updateProjectionMatrix();
}
addEventListener('resize', resize);

// ===== メインループ =====
let lastT = performance.now();
function tick(now) {
  const dt = now - lastT;
  lastT = now;
  resize();

  // 落下アニメーション(ease-out + 軽いバウンド)
  for (let i = anims.length - 1; i >= 0; i--) {
    const a = anims[i];
    a.t += dt;
    let k = Math.min(1, a.t / a.dur);
    k = 1 - Math.pow(1 - k, 3);
    let yv = a.from + (a.to - a.from) * k;
    if (a.t > a.dur * 0.82) {
      const b = (a.t - a.dur * 0.82) / (a.dur * 0.18);
      yv += Math.sin(b * Math.PI) * 0.07;
    }
    a.mesh.position.y = yv;
    if (a.t >= a.dur) { a.mesh.position.y = a.to; anims.splice(i, 1); }
  }

  if (pointerInside) setHover(pickColumn());

  // 直前手リング・候補手リングを常にカメラへ向ける
  if (ring.visible) ring.quaternion.copy(camera.quaternion);
  for (const r of candRings) if (r.visible) r.quaternion.copy(camera.quaternion);

  // 思考中の経過秒
  if (busy && thinkStart && !$('thinking').classList.contains('hidden')) {
    $('elapsed').textContent = ((now - thinkStart) / 1000).toFixed(1) + ' 秒';
  }

  controls.update();
  renderer.render(scene, camera);
  requestAnimationFrame(tick);
}
requestAnimationFrame(tick);
