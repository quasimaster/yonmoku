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
console.log('  profiles:', ready.profiles.map((p) => `${p.id}:${p.name}[${p.plies.join('/')}]`).join(' '));

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

console.log(`\n==== ${fail === 0 ? 'ALL PASS' : 'FAILED'} (${fail} failures) ====`);
process.exit(fail === 0 ? 0 : 1);
