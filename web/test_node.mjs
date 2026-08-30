// WASM ビルドの動作確認と native 比の速度実測(Node.js 用)。
//   node web/test_node.mjs [profile...]
import YonmokuModule from './yonmoku.js';

const M = await YonmokuModule();

const c = (name, ret, args) => M.cwrap(name, ret, args);
const api = {
  init:        c('yon_init', null, []),
  newGame:     c('yon_new_game', null, ['number', 'number']),
  play:        c('yon_play', 'number', ['number', 'number']),
  think:       c('yon_think', 'number', []),
  analyze:     c('yon_analyze', 'number', []),
  undo:        c('yon_undo', 'number', []),
  status:      c('yon_status', 'number', []),
  turn:        c('yon_turn', 'number', []),
  moveCount:   c('yon_move_count', 'number', []),
  blackToMove: c('yon_black_to_move', 'number', []),
  lastScore:   c('yon_last_score', 'number', []),
  lastMs:      c('yon_last_ms', 'number', []),
  lastNodes:   c('yon_last_nodes', 'number', []),
  winRate:     c('yon_win_rate_black', 'number', []),
  landingZ:    c('yon_landing_z', 'number', ['number', 'number']),
  legal:       c('yon_legal_columns', 'number', []),
  profileNum:  c('yon_profile_num', 'number', []),
  profileName: c('yon_profile_name', 'string', ['number']),
  profilePlies:c('yon_profile_plies', 'number', ['number', 'number']),
};
// ★i64 の戻り値は符号付き BigInt として渡ってくる。bit63(マス 3,3,3)が立つと負値になり、
//   そのまま popcount すると無限ループするので必ず asUintN(64) で符号を落とす。
const u64 = (v) => BigInt.asUintN(64, v);
const black = () => u64(M._yon_black());
const white = () => u64(M._yon_white());
const winLine = () => u64(M._yon_win_line());

const pc = (v) => { let n = 0n, x = u64(v); while (x) { x &= x - 1n; n++; } return Number(n); };

let fail = 0;
const check = (ok, msg) => { console.log(`  [${ok ? 'OK' : 'NG'}] ${msg}`); if (!ok) fail++; };

api.init();

console.log('=== profiles ===');
for (let i = 0; i < api.profileNum(); i++) {
  console.log(`  ${i} ${api.profileName(i)}: N = ${[0,1,2,3].map(b => api.profilePlies(i, b)).join('/')}`);
}
check(api.profilePlies(3, 0) === 10 && api.profilePlies(3, 3) === 26, 'profile 3 == current CLI');

console.log('\n=== full game (profile 0) ===');
api.newGame(1, 0);
let guard = 0;
while (api.status() === 0 && guard++ < 70) { if (api.think() < 0) break; }
console.log(`  moves=${api.moveCount()} status=${api.status()}`);
check(api.status() !== 0, 'game finished');
check(api.moveCount() === pc(black()) + pc(white()), 'stone count matches move count');
if (api.status() === 1 || api.status() === 2) check(pc(winLine()) === 4, 'win line has 4 cells');

console.log('\n=== undo ===');
api.newGame(1, 0);
api.play(0, 0); api.think(); api.play(1, 1); api.think();
const before = api.moveCount();
const after = api.undo();
check(before === 4 && after === 2, `undo 4 -> 2 (got ${before} -> ${after})`);
check(api.blackToMove() === 1, 'human(black) to move again');
check(api.landingZ(1, 1) === 0, 'undone cell is empty');

console.log('\n=== analyze does not mutate ===');
api.newGame(1, 0); api.play(0, 0);
const b0 = black(), w0 = white(), mc = api.moveCount();
const sq = api.analyze();
check(sq >= 0 && api.moveCount() === mc && black() === b0 && white() === w0, 'board unchanged by analyze');

console.log('\n=== speed (AI vs AI full game per profile) ===');
const want = process.argv.slice(2).map(Number);
const ids = want.length ? want : [0, 1, 2, 3];
console.log('id  name        plies            moves   total_s    max_ms    avg_ms          nodes');
console.log('--------------------------------------------------------------------------------------');
for (const i of ids) {
  api.newGame(0, i);
  let total = 0, mx = 0, nodes = 0, moves = 0, g = 0;
  while (api.status() === 0 && g++ < 70) {
    if (api.think() < 0) break;
    const ms = api.lastMs();
    total += ms; nodes += api.lastNodes(); if (ms > mx) mx = ms; moves++;
  }
  const plies = [0,1,2,3].map(b => api.profilePlies(i, b)).join('/');
  console.log(
    `${String(i).padEnd(3)} ${api.profileName(i).padEnd(10)} ${plies.padEnd(15)} ${String(moves).padStart(5)} ` +
    `${(total/1000).toFixed(2).padStart(9)} ${mx.toFixed(0).padStart(9)} ${(total/moves).toFixed(1).padStart(9)} ${nodes.toFixed(0).padStart(14)}`);
}

console.log(`\n==== ${fail === 0 ? 'ALL PASS' : 'FAILED'} (${fail} failures) ====`);
process.exit(fail === 0 ? 0 : 1);
