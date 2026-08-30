// code/web/bench_fixed.cpp と同一の局面・同一の探索を WASM で走らせる。
// ノード数が native と一致することを確認したうえで、時間比を native/WASM の速度比として読む。
//   node web/bench_fixed.mjs
import YonmokuModule from './yonmoku.js';

const M = await YonmokuModule();
const c = (n, r, a) => M.cwrap(n, r, a);
const api = {
  init:      c('yon_init', null, []),
  newGame:   c('yon_new_game', null, ['number', 'number']),
  analyze:   c('yon_analyze', 'number', []),
  lastMs:    c('yon_last_ms', 'number', []),
  lastNodes: c('yon_last_nodes', 'number', []),
  lastScore: c('yon_last_score', 'number', []),
  turn:      c('yon_turn', 'number', []),
};

const GAME = '000000003322222230033231030320101010031113111131102101210121210113221313113223233333012333323223313130202020121212120202';
const PLIES = [0, 6, 14, 24, 34, 44];
const PROFILE = 3;

api.init();
console.log('   plies   turn        nodes           ms      score');
console.log('--------------------------------------------------------');

for (const n of PLIES) {
  const xy = [];
  for (let i = 0; i < n; i++) { xy.push(+GAME[i * 2], +GAME[i * 2 + 1]); }

  // int 配列を WASM ヒープへ
  const bytes = xy.length * 4;
  const ptr = M._malloc(Math.max(bytes, 4));
  if (bytes) M.HEAP32.set(Int32Array.from(xy), ptr >> 2);
  api.newGame(1, PROFILE);
  const loaded = M.ccall('yon_load', 'number', ['number', 'number'], [ptr, xy.length]);
  M._free(ptr);
  if (loaded < 0) { console.log(`load failed at plies=${n}`); continue; }

  api.analyze();
  console.log(
    `${String(n).padStart(8)} ${String(api.turn()).padStart(6)} ` +
    `${api.lastNodes().toFixed(0).padStart(12)} ${api.lastMs().toFixed(1).padStart(12)} ${String(api.lastScore()).padStart(10)}`);
}
