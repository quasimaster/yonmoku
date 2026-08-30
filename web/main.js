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

// ===== 状態 =====
let S = null;              // worker から届いた最新の state
let profiles = [];
let busy = true;           // AI 思考中 or 起動中
let hoverCol = -1;         // ホバー中の列 index(x + y*4)
let keyCol = 5;            // キーボード選択中の列
let thinkStart = 0;
const anims = [];          // 落下アニメーション

// ===== Worker =====
const worker = new Worker(new URL('./worker.js', import.meta.url), { type: 'module' });
worker.onerror = (e) => fatal('エンジンの読み込みに失敗しました: ' + (e.message || e.filename || 'unknown error'));
worker.onmessage = (e) => handle(e.data);
worker.postMessage({ type: 'init' });

function handle(m) {
  switch (m.type) {
    case 'ready':
      profiles = m.profiles;
      buildProfileSelect(m.defaultProfile);
      $('boot').classList.add('hidden');
      busy = false;
      newGame();
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
    case 'error':
      fatal('エンジンでエラーが発生しました: ' + m.message);
      break;
    default:
      break;
  }
}

// ===== 難易度セレクト =====
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
  sel.value = String(def);
  updateProfileHint();
}

function updateProfileHint() {
  const p = profiles[Number($('profile').value)];
  if (!p) return;
  const heavy = p.plies[0] >= 12;
  const detail = `序盤 ${p.plies[0]} / 中盤 ${p.plies[1]}・${p.plies[2]} / 終盤 ${p.plies[3]} 手読み`;
  $('profile').title = detail + (heavy ? '\n※ 1手に十数秒かかることがあります' : '');
  $('profilehint').textContent = detail + (heavy ? '　※ 1手に十数秒かかることがあります' : '');
}

// ===== 状態の反映 =====
function applyState(s) {
  const prev = S;
  S = s;

  syncStones(prev);
  updateRing();
  updateHUD();

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

  const who = S.blackToMove ? '黒' : '白';
  const isHuman = S.blackToMove === S.humanIsBlack;
  $('turnwho').textContent = S.status === 0 ? `${who}(${isHuman ? 'あなた' : 'AI'})` : '—';

  // 評価値(常に黒視点。設計書 §4.6.1)
  const card = $('evalcard');
  if (!S.evalValid) {
    $('score').textContent = '—';
    $('wr-black').textContent = '黒 50.0%';
    $('wr-white').textContent = '50.0% 白';
    $('winbar-black').style.width = '50%';
    $('thinktime').textContent = '—';
    $('nodes').textContent = '—';
    $('evalfresh').textContent = '';
    $('evalfresh').className = 'tag';
    card.classList.remove('stale');
    $('evalnote').textContent = 'AI が最初の手を考えると評価値が表示されます。';
  } else {
    const wr = Math.max(0, Math.min(100, S.winRateBlack));
    $('winbar-black').style.width = wr.toFixed(1) + '%';
    $('wr-black').textContent = `黒 ${wr.toFixed(1)}%`;
    $('wr-white').textContent = `${(100 - wr).toFixed(1)}% 白`;
    $('score').textContent = S.isMate
      ? (S.scoreBlack > 0 ? '黒 勝ち確定' : '白 勝ち確定')
      : (S.scoreBlack > 0 ? `黒 +${S.scoreBlack}` : `白 +${-S.scoreBlack}`);
    $('thinktime').textContent = (S.lastMs / 1000).toFixed(2) + ' 秒';
    $('nodes').textContent = S.lastNodes >= 0 ? Math.round(S.lastNodes).toLocaleString() : '—';

    // 人間の手番中は「AI が前回思考した時点の値」なので、古いことを明示する
    const stale = S.status === 0 && isHuman;
    card.classList.toggle('stale', stale);
    $('evalfresh').textContent = stale ? 'AI 前回思考時点' : '最新';
    $('evalfresh').className = stale ? 'tag stale' : 'tag';
    $('evalnote').textContent = stale
      ? 'あなたの手番中は、AI が直前に読んだ時点の評価値を表示しています。'
      : '';
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
  const humanTurn = S && S.status === 0 && S.blackToMove === S.humanIsBlack;
  $('undo').disabled = busy || !S || S.moveCount === 0;
  $('profile').disabled = busy;
  $('side').disabled = busy;
  canvas.style.cursor = humanTurn && !busy ? (hoverCol >= 0 ? 'pointer' : 'grab') : 'default';
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
  if (S.blackToMove !== S.humanIsBlack) return -1;
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
    ghost.material.color.set(S.humanIsBlack ? 0x5a6472 : 0xdfe4ea);
    ghost.visible = true;
  } else {
    ghost.visible = false;
  }
  refreshButtons();
}

function playColumn(col) {
  if (col < 0 || !S || busy) return;
  if (S.status !== 0 || S.blackToMove !== S.humanIsBlack) return;
  if (S.landing[col] < 0) return;
  busy = true;
  setHover(-1);
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
  worker.postMessage({ type: 'undo' });
});
$('profile').addEventListener('change', () => {
  updateProfileHint();
  if (!S) return;
  worker.postMessage({ type: 'setProfile', profile: Number($('profile').value) });
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
  };
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

  // 直前手リングを常にカメラへ向ける
  if (ring.visible) ring.quaternion.copy(camera.quaternion);

  // 思考中の経過秒
  if (busy && thinkStart && !$('thinking').classList.contains('hidden')) {
    $('elapsed').textContent = ((now - thinkStart) / 1000).toFixed(1) + ' 秒';
  }

  controls.update();
  renderer.render(scene, camera);
  requestAnimationFrame(tick);
}
requestAnimationFrame(tick);
