// worker.js のメッセージプロトコルを Node で検証する(ブラウザ無しで UI 側の契約を確認する)。
//   node web/test_worker.mjs
// Worker 環境(self / postMessage)を最小限だけ模倣し、
// main.js が実際に送るのと同じ順序でメッセージを流して state の整合性を見る。

const inbox = [];
globalThis.self = {
  postMessage: (m) => inbox.push(m),
  set onmessage(fn) { globalThis.__onmessage = fn; },
  get onmessage() { return globalThis.__onmessage; },
};

await import('./worker.js');

const send = (m) => globalThis.__onmessage({ data: m });
const waitFor = async (type, timeoutMs = 120000) => {
  const t0 = Date.now();
  for (;;) {
    const i = inbox.findIndex((m) => m.type === type);
    if (i >= 0) return inbox.splice(i, 1)[0];
    if (Date.now() - t0 > timeoutMs) throw new Error(`timeout waiting for ${type}`);
    await new Promise((r) => setTimeout(r, 5));
  }
};

let fail = 0;
const check = (ok, msg) => { console.log(`  [${ok ? 'OK' : 'NG'}] ${msg}`); if (!ok) fail++; };

console.log('=== ready ===');
send({ type: 'init' });
const ready = await waitFor('ready');
check(Array.isArray(ready.profiles) && ready.profiles.length === 6, `6 profiles advertised`);
check(ready.profiles[3].plies.join('/') === '10/10/12/26', 'default profile == current CLI');
check(ready.profiles[3].rows.map((r) => r.join(':')).join(' ') === '1:10 21:10 29:12 37:26',
      'profile rows are opened into a schedule');
console.log('  profiles:', ready.profiles.map((p) => `${p.id}:${p.name}[${p.plies.join('/')}]`).join(' '));

check(Array.isArray(ready.models) && ready.models.length === 5, `5 models advertised (${ready.models.length})`);
check(ready.models.map((m) => `${m.name}/${m.weights}`).join(' ')
      === 'alpha/ver7.2 alpha/ver8.1 alpha/ver8.2 alpha/ver8.2.5 core/ver1.0', 'model list');
check(ready.models.every((m) => m.available), 'every weights file loaded');
check(ready.defaultModel === 0, `default model = ${ready.defaultModel} (alpha / builtin ver7.2)`);
console.log('  models:', ready.models.map((m) => `${m.id}:${m.name}[${m.weights}]${m.available ? '' : '(NA)'}`).join(' '));
check(ready.limits.maxRows === 8 && ready.limits.maxPly === 30 && ready.limits.minPly === 2,
      `limits = ${JSON.stringify(ready.limits)}`);

console.log('\n=== new game (human = black, profile 0) ===');
send({ type: 'newGame', humanIsBlack: true, profile: 0 });
let s = await waitFor('state');
check(s.black.length === 0 && s.white.length === 0, 'empty board');
check(s.legal === 0xffff, 'all 16 columns legal');
check(s.landing.every((z) => z === 0), 'all landings at z=0');
check(s.blackToMove === true && s.humanIsBlack === true, 'human(black) to move');
check(s.evalValid === false, 'no evaluation yet');

console.log('\n=== human plays, AI replies ===');
send({ type: 'play', x: 0, y: 0 });
await waitFor('played');
s = await waitFor('state');
check(s.black.length === 1 && s.black[0] === 0, 'black stone at sq 0');
check(s.landing[0] === 1, 'next stone in that column lands at z=1');
check(s.blackToMove === false, 'white(AI) to move');

send({ type: 'think' });
await waitFor('thinking');
const moved = await waitFor('moved');
s = await waitFor('state');
check(moved.sq >= 0 && moved.sq < 64, `AI moved to sq ${moved.sq}`);
check(s.white.length === 1, 'white has 1 stone');
check(s.evalValid === true, 'evaluation now valid');
check(typeof s.scoreBlack === 'number', `scoreBlack = ${s.scoreBlack}`);
check(s.winRateBlack >= 0 && s.winRateBlack <= 100, `winRateBlack = ${s.winRateBlack.toFixed(1)}%`);
check(s.lastSq === moved.sq, 'lastSq matches the AI move');
check(s.hand.length === 2, 'hand has 2 moves');

console.log('\n=== undo ===');
send({ type: 'undo' });
s = await waitFor('state');
check(s.moveCount === 0, `undo removed AI move + human move (moveCount=${s.moveCount})`);
check(s.black.length === 0 && s.white.length === 0, 'board is empty again');

console.log('\n=== profile switch ===');
send({ type: 'setProfile', profile: 2 });
s = await waitFor('state');
check(s.profile === 2, 'profile switched to 2');
check(s.schedule.map((r) => r.join(':')).join(' ') === '1:8 21:8 29:10 37:20', 'schedule follows the profile');

console.log('\n=== model switch ===');
const coreId = ready.models.findIndex((m) => m.name === 'core');
send({ type: 'setModel', model: coreId });
let r = await waitFor('model');
s = await waitFor('state');
check(r.ok === true && s.model === coreId, 'switched to core');
send({ type: 'setModel', model: 3 });          // alpha ver8.2.5(エンジンは同じで重みだけ変わる)
await waitFor('model');
s = await waitFor('state');
check(s.model === 3, 'switched to alpha ver8.2.5');
send({ type: 'setModel', model: 0 });
await waitFor('model');
s = await waitFor('state');
check(s.model === 0, 'switched back to the default');

console.log('\n=== custom schedule ===');
send({ type: 'setSchedule', rows: [[1, 4], [12, 6], [24, 8]] });
r = await waitFor('schedule');
s = await waitFor('state');
check(r.ok === true, 'valid schedule accepted');
check(s.profile === -1, 'profile becomes -1 (custom)');
check(s.schedule.map((x) => x.join(':')).join(' ') === '1:4 12:6 24:8', 'schedule reported back');
check(s.currentPly === 4, `currentPly = ${s.currentPly} at turn ${s.turn}`);

send({ type: 'setSchedule', rows: [[1, 9]] });
r = await waitFor('schedule');
s = await waitFor('state');
check(r.ok === false && r.code === -4, 'odd plies rejected (-4)');
check(s.schedule.map((x) => x.join(':')).join(' ') === '1:4 12:6 24:8', 'rejected schedule leaves the previous one');

console.log('\n=== custom schedule survives newGame(profile -1) ===');
send({ type: 'newGame', humanIsBlack: true, profile: -1 });
s = await waitFor('state');
check(s.schedule.map((x) => x.join(':')).join(' ') === '1:4 12:6 24:8', 'schedule kept');
check(s.profile === -1, 'still custom');

console.log('\n=== full AI vs AI game via protocol (profile 0) ===');
send({ type: 'newGame', humanIsBlack: false, profile: 0 });
s = await waitFor('state');
let guard = 0;
while (s.status === 0 && guard++ < 70) {
  send({ type: 'think' });
  await waitFor('thinking');
  await waitFor('moved');
  s = await waitFor('state');
}
console.log(`  finished: moves=${s.moveCount} status=${s.status}`);
check(s.status !== 0, 'game reached a terminal state');
check(s.legal === 0, 'no legal columns reported after the game ends');
if (s.status === 1 || s.status === 2) check(s.winLine.length === 4, 'winLine has 4 cells');
check(s.black.length + s.white.length === s.moveCount, 'stones match move count');

// 盤面の整合性: 各列で石は下から詰まっていること(重力)
let gravityOk = true;
const occupied = new Set([...s.black, ...s.white]);
for (let y = 0; y < 4; y++) for (let x = 0; x < 4; x++) {
  let seenEmpty = false;
  for (let z = 0; z < 4; z++) {
    const has = occupied.has(x + y * 4 + z * 16);
    if (!has) seenEmpty = true;
    else if (seenEmpty) gravityOk = false;   // 空の上に石がある = 浮いている
  }
}
check(gravityOk, 'no floating stones (gravity holds in every column)');


// ===== 研究モード(反復深化 + 上位 K 手) =====
//   設計: docs/設計書/Web公開/implementation-plan-research-analysis.md §7.2
console.log('\n=== research mode ===');
{
  check(ready.limits.anaMaxK >= 3 && ready.limits.anaMaxPly === 64,
        `analysis limits = K<=${ready.limits.anaMaxK} / N<=${ready.limits.anaMaxPly}`);

  // 任意局面まで白黒を交互に並べる(AI には一切指させない)
  send({ type: 'newGame', humanIsBlack: true, profile: 0 });
  s = await waitFor('state');
  const OPENING = [[1,1],[2,2],[1,2],[2,1],[0,0],[3,3],[1,1],[2,2],[2,1],[1,2],[0,3],[3,0]];
  for (const [x, y] of OPENING) {
    send({ type: 'play', x, y });
    await waitFor('played');
    s = await waitFor('state');
  }
  check(s.moveCount === OPENING.length, `${OPENING.length} moves placed by hand (${s.moveCount})`);
  check(s.black.length === 6 && s.white.length === 6, 'both colours placed by the operator');
  check(inbox.filter((m) => m.type === 'moved').length === 0, 'the AI never moved on its own');

  // 8 → 10 → 12 と深めて、途中で停止する
  inbox.length = 0;
  send({ type: 'analyzeStart', startPly: 8, topK: 3, freshTt: false, deadlineMs: 0, seed: 12345 });
  const iters = [];
  for (let i = 0; i < 3; i++) {
    const it = await waitFor('analyzeIter');
    iters.push(it);
    await waitFor('state');
  }
  check(iters.map((i) => i.ply).join(',') === '8,10,12', `iterations arrive in order (${iters.map((i) => i.ply).join(',')})`);
  check(iters.every((i) => i.complete === true), 'every iteration completed');
  check(iters.every((i) => i.moves.length === 3), 'three candidates per iteration');
  check(iters.every((i) => i.moves.every((m, k, a) => k === 0 || a[k - 1].scoreBlack >= m.scoreBlack)),
        'candidates are sorted by score');
  check(iters.every((i) => i.rootMoves > 0 && i.nodes > 0), 'rootMoves / nodes reported');
  for (const it of iters) {
    console.log(`  N=${String(it.ply).padStart(2)}  ` +
                it.moves.map((m, k) => `${k + 1}.sq${m.sq}=${m.scoreBlack}`).join('  ') +
                `  ${it.ms.toFixed(0)} ms`);
  }

  // ★停止は反復の合間にしか効かない。送ったあと次の analyzeEnd が来ることを見る
  send({ type: 'analyzeStop' });
  const end = await waitFor('analyzeEnd');
  check(end.reason === 'stopped', `stop request ends the loop (reason=${end.reason})`);

  const after = inbox.filter((m) => m.type === 'analyzeIter').length;
  await new Promise((r) => setTimeout(r, 200));
  check(inbox.filter((m) => m.type === 'analyzeIter').length === after, 'no further iterations after the end');

  // 解析は盤面を変えない
  const s2 = await (async () => { send({ type: 'undoOne' }); return waitFor('state'); })();
  check(s2.moveCount === OPENING.length - 1, `undoOne rewinds exactly one move (${s2.moveCount})`);

  // 読み手数が空きマス数を超えたら「全読み」で自動終了する
  //   ★上限手数は設けていないので、この自動終了と solved と人の停止だけが終わり方
  inbox.length = 0;
  const empty = 64 - s2.moveCount;
  send({ type: 'analyzeStart', startPly: empty + 2, topK: 3, freshTt: false, deadlineMs: 0, seed: 12345 });
  const e2 = await waitFor('analyzeEnd');
  check(e2.reason === 'exhausted',
        `N > 空きマス(${empty})は全読み扱いで自動終了する (reason=${e2.reason})`);

  // 終局局面は解析できない
  send({ type: 'newGame', humanIsBlack: true, profile: 0 });
  s = await waitFor('state');
  let guard2 = 0;
  while (s.status === 0 && guard2++ < 70) {
    const col = s.landing.findIndex((z) => z >= 0);
    if (col < 0) break;
    send({ type: 'play', x: col % 4, y: Math.floor(col / 4) });
    await waitFor('played');
    s = await waitFor('state');
  }
  inbox.length = 0;
  send({ type: 'analyzeStart', startPly: 8, topK: 3, freshTt: false, deadlineMs: 0, seed: 12345 });
  const e3 = await waitFor('analyzeEnd');
  check(s.status !== 0 && e3.reason === 'invalid', `終局局面は解析できない (reason=${e3.reason})`);
}

console.log(`\n==== ${fail === 0 ? 'ALL PASS' : 'FAILED'} (${fail} failures) ====`);
process.exit(fail === 0 ? 0 : 1);
