// WASM ビルドの動作確認と native 比の速度実測(Node.js 用)。
//   node web/test_node.mjs [profile...]
import YonmokuModule from './yonmoku.js';

const M = await YonmokuModule();

const c = (name, ret, args) => M.cwrap(name, ret, args);
const api = {
  init:        c('yon_init', null, []),
  seed:        c('yon_set_seed', null, ['number']),
  newGame:     c('yon_new_game', null, ['number', 'number']),
  setProfile:  c('yon_set_profile', null, ['number']),
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
  profileTurn: c('yon_profile_turn', 'number', ['number']),
  profileCur:  c('yon_profile_current', 'number', []),
  setModel:    c('yon_set_model', 'number', ['number']),
  modelNum:    c('yon_model_num', 'number', []),
  modelCur:    c('yon_model_current', 'number', []),
  modelName:   c('yon_model_name', 'string', ['number']),
  modelWeights:c('yon_model_weights', 'string', ['number']),
  modelAvail:  c('yon_model_available', 'number', ['number']),
  modelDefault:c('yon_model_default', 'number', []),
  setSchedule: c('yon_set_schedule', 'number', ['number', 'number', 'number']),
  schedLen:    c('yon_schedule_len', 'number', []),
  schedTurn:   c('yon_schedule_turn', 'number', ['number']),
  schedPly:    c('yon_schedule_ply', 'number', ['number']),
  schedMaxRows:c('yon_schedule_max_rows', 'number', []),
  schedMaxPly: c('yon_schedule_max_ply', 'number', []),
  currentPly:  c('yon_current_ply', 'number', []),
  // --- 研究モード ---
  analyzePly:  c('yon_analyze_ply', 'number', ['number', 'number', 'number', 'number']),
  anaPly:      c('yon_ana_ply', 'number', []),
  anaCount:    c('yon_ana_count', 'number', []),
  anaSq:       c('yon_ana_sq', 'number', ['number']),
  anaScore:    c('yon_ana_score', 'number', ['number']),
  anaWinrate:  c('yon_ana_winrate', 'number', ['number']),
  anaTied:     c('yon_ana_tied', 'number', []),
  anaForced:   c('yon_ana_forced', 'number', []),
  anaComplete: c('yon_ana_complete', 'number', []),
  anaMs:       c('yon_ana_ms', 'number', []),
  anaNodes:    c('yon_ana_nodes', 'number', []),
  anaRootMoves:c('yon_ana_root_moves', 'number', []),
  undoOne:     c('yon_undo_one', 'number', []),
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

// ★AI は「最善評価が並んだ手」をグローバル rng でランダムに 1 つ選ぶ(ai_player_pvs_inc_id.hpp:587)。
//   rng は対局をまたいでも巻き戻らないので、シードを固定しないと 2 局目以降の結果が毎回変わる。
const SEED = 12345;
api.seed(SEED);

console.log('=== reproducibility ===');
{
  const play = () => { let g = 0, n = 0; while (api.status() === 0 && g++ < 70) { if (api.think() < 0) break; n += api.lastNodes(); } return `${api.moveCount()}/${n}`; };
  api.seed(SEED); api.newGame(0, 0); const a = play();
  api.seed(SEED); api.newGame(0, 0); const b = play();
  api.newGame(0, 0); const cNoSeed = play();   // シードを戻さない = rng が進んだまま
  check(a === b, `same seed reproduces the game (${a} == ${b})`);
  console.log(`  without reseeding: ${cNoSeed}${cNoSeed === a ? '' : '  <- 乱数が進んでいるので変わる(仕様)'}`);
}

console.log('\n=== profiles ===');
for (let i = 0; i < api.profileNum(); i++) {
  console.log(`  ${i} ${api.profileName(i)}: N = ${[0,1,2,3].map(b => api.profilePlies(i, b)).join('/')}`);
}
check(api.profilePlies(3, 0) === 10 && api.profilePlies(3, 3) === 26, 'profile 3 == current CLI');
check([0,1,2,3].map(b => api.profileTurn(b)).join('/') === '1/21/29/37', 'bucket turns are 1/21/29/37');

console.log('\n=== models ===');
for (let i = 0; i < api.modelNum(); i++) {
  console.log(`  ${i} ${api.modelName(i)}: weights=${api.modelWeights(i) || '(none)'} available=${api.modelAvail(i)}`);
}
const modelNames = [...Array(api.modelNum())].map((_, i) => `${api.modelName(i)}/${api.modelWeights(i)}`);
const coreId = modelNames.findIndex((s) => s.startsWith('core/'));
check(api.modelNum() === 5, `5 models advertised (${api.modelNum()})`);
check(modelNames.join(' ') === 'alpha/ver7.2 alpha/ver8.1 alpha/ver8.2 alpha/ver8.2.5 core/ver1.0',
      `model list = ${modelNames.join(' ')}`);
check([...Array(api.modelNum())].every((_, i) => api.modelAvail(i) === 1), 'every weights file loaded');
check(api.modelDefault() === 0 && api.modelWeights(0) === 'ver7.2', 'default is alpha + builtin ver7.2');
check(api.setModel(coreId) === 0 && api.modelCur() === coreId, 'switch to core');
check(api.setModel(2) === 0 && api.modelCur() === 2, 'switch to alpha ver8.2');
check(api.setModel(0) === 0 && api.modelCur() === 0, 'switch back to the default');
check(api.setModel(99) === -1, 'unknown model rejected');

// 重みを変えると実際に着手が変わることを確かめる(同一局面で ver7.2 と ver8.2.5 を比べる)
const firstMoves = [];
for (let i = 0; i < api.modelNum(); i++) {
  api.setModel(i);
  api.newGame(0, 1);
  firstMoves.push(api.analyze());
}
api.setModel(0);
console.log('  first move by model:', firstMoves.map((sq, i) => `${modelNames[i]}=${sq}`).join(' '));
check(new Set(firstMoves).size >= 2, 'different weights do not all produce the same move');

console.log('\n=== schedule ===');
const maxRows = api.schedMaxRows();
const tPtr = M._malloc(maxRows * 4), pPtr = M._malloc(maxRows * 4);
const setSched = (rows) => {
  rows.forEach(([t, p], i) => { M.HEAP32[(tPtr >> 2) + i] = t; M.HEAP32[(pPtr >> 2) + i] = p; });
  return api.setSchedule(tPtr, pPtr, rows.length);
};
const readSched = () => [...Array(api.schedLen())].map((_, i) => `${api.schedTurn(i)}:${api.schedPly(i)}`).join(' ');

api.setProfile(3);
check(readSched() === '1:10 21:10 29:12 37:26', `profile 3 fills the schedule (${readSched()})`);
check(api.profileCur() === 3, 'profile 3 is current');
check(setSched([[1, 9]]) === -4, 'odd plies rejected');
check(setSched([[1, 32]]) === -4, 'plies over the max rejected');
check(setSched([[1, 0]]) === -4, 'plies under the min rejected');
check(setSched([[2, 10]]) === -2, 'first row must start at turn 1');
check(setSched([[1, 10], [5, 10], [3, 10]]) === -3, 'descending turns rejected');
check(setSched([[1, 10], [5, 10], [5, 12]]) === -3, 'duplicate turns rejected');
check(setSched(Array.from({ length: maxRows + 1 }, (_, i) => [i + 1, 4])) === -1, 'too many rows rejected');
check(readSched() === '1:10 21:10 29:12 37:26', 'a rejected schedule leaves the previous one intact');

check(setSched([[1, 4], [3, 6], [5, 8]]) === 0, 'valid custom schedule accepted');
check(api.profileCur() === -1, 'custom schedule switches the profile to -1');
api.newGame(1, -1);
check(readSched() === '1:4 3:6 5:8', 'new game with profile -1 keeps the custom schedule');
check(api.currentPly() === 4, `turn 1 uses 4 plies (got ${api.currentPly()})`);
// 指定の turn まで、空いている列へ順に置いて進める(四目が揃わない列から選ぶ必要は無い:
// 途中で終局したらそこで止まるので、その場合はテストを飛ばす)
const advanceTo = (turn) => {
  while (api.status() === 0 && api.turn() < turn) {
    let played = false;
    for (let col = 0; col < 16 && !played; col++) {
      const x = col % 4, y = (col / 4) | 0;
      if (api.landingZ(x, y) >= 0) played = api.play(x, y) !== 2;
    }
    if (!played) break;
  }
  return api.turn();
};
check(advanceTo(3) === 3 && api.currentPly() === 6, `turn 3 uses 6 plies (got ${api.currentPly()})`);
check(advanceTo(5) === 5 && api.currentPly() === 8, `turn 5 uses 8 plies (got ${api.currentPly()})`);
check(advanceTo(7) === 7 && api.currentPly() === 8, `turn 7 still uses the last row (got ${api.currentPly()})`);

check(setSched([[1, 2]]) === 0, 'single-row N=2 schedule accepted');
api.newGame(0, -1);
let g2 = 0;
while (api.status() === 0 && g2++ < 70) { if (api.think() < 0) break; }
check(api.status() !== 0, `N=2 game finishes (${api.moveCount()} moves)`);
api.setProfile(3);   // 以降のテストのために標準へ戻す

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


// ===== 研究モード(任意局面の反復深化解析 + 上位 K 手) =====
//   設計: docs/設計書/Web公開/implementation-plan-research-analysis.md §7.2
console.log('\n=== research mode ===');
{
  const OPENING = [1,1, 2,2, 1,2, 2,1, 0,0, 3,3, 1,1, 2,2, 2,1, 1,2, 0,3, 3,0];
  const setup = (humanIsBlack) => {
    api.newGame(humanIsBlack, -1);
    api.seed(SEED);
    for (let i = 0; i < OPENING.length; i += 2) api.play(OPENING[i], OPENING[i + 1]);
  };
  const cands = () => {
    const out = [];
    for (let i = 0; i < api.anaCount(); i++) {
      out.push({ sq: api.anaSq(i), score: api.anaScore(i), wr: api.anaWinrate(i) });
    }
    return out;
  };

  setup(1);
  const mc = api.moveCount(), bb = black(), wb = white();
  check(api.analyzePly(8, 3, 1, 0) === 1, 'analyzePly(8) returns complete');
  check(api.moveCount() === mc && black() === bb && white() === wb, 'analyze does not touch the board');
  check(api.anaPly() === 8 && api.anaCount() === 3, `N=8 with 3 candidates (${api.anaPly()}/${api.anaCount()})`);

  // 反復深化の梯子。前の深さのセッションを引き継ぐ(fresh_tt = 0)
  const rows = [];
  let mono = true, prevNodes = 0;
  for (let n = 8; n <= 14; n += 2) {
    if (api.analyzePly(n, 3, 0, 0) !== 1) { mono = false; break; }
    const c = cands();
    rows.push({ n, ms: api.anaMs(), nodes: api.anaNodes(), best: c[0] });
    if (api.anaNodes() <= prevNodes) mono = false;
    prevNodes = api.anaNodes();
  }
  check(rows.length === 4, `ladder N=8..14 ran (${rows.length} iterations)`);
  check(mono, 'nodes increase monotonically as N deepens');
  for (const r of rows) {
    const c = r.best;
    console.log(`  N=${String(r.n).padStart(2)}  best=(${c.sq % 4 + 1},${Math.floor(c.sq / 4) % 4 + 1})` +
                `  score(black)=${String(c.score).padStart(7)}  win=${c.wr.toFixed(1)}%` +
                `  ${r.ms.toFixed(0).padStart(6)} ms  ${r.nodes.toFixed(0).padStart(10)} nodes`);
  }

  // 候補手は評価値の降順に並んでいること
  setup(1);
  api.analyzePly(10, 3, 1, 0);
  const c3 = cands();
  check(c3.length === 3 && c3[0].score >= c3[1].score && c3[1].score >= c3[2].score,
        `candidates are sorted (${c3.map(x => x.score).join(' >= ')})`);

  // 再現性
  setup(1);
  api.analyzePly(10, 3, 1, 0);
  const a = cands().map(x => `${x.sq}:${x.score}`).join(',');
  setup(1);
  api.analyzePly(10, 3, 1, 0);
  const b = cands().map(x => `${x.sq}:${x.score}`).join(',');
  check(a === b, `same setup reproduces the analysis (${a})`);

  // ★先後エントリが手番に追従する(g_human_is_black に依存しない)
  setup(0);
  api.analyzePly(10, 3, 1, 0);
  const w = cands().map(x => `${x.sq}:${x.score}`).join(',');
  check(a === w, 'analysis does not depend on humanIsBlack');

  // 引数チェック
  check(api.analyzePly(9, 3, 0, 0) === -2, 'odd N rejected');
  check(api.analyzePly(8, 0, 0, 0) === -2 && api.analyzePly(8, 9, 0, 0) === -2, 'top_k out of range rejected');
  check(api.analyzePly(66, 3, 0, 0) === -2, 'N over 64 rejected');

  // deadline(1 ms ならまず完走しない)
  setup(1);
  const dl = api.analyzePly(16, 3, 1, 1);
  check(dl === 0 && api.anaComplete() === 0 && api.anaCount() >= 1,
        `deadline stops mid-iteration and still reports a best move (ret=${dl})`);

  // undoOne は 1 手ずつ
  setup(1);
  const n0 = api.moveCount();
  check(api.undoOne() === n0 - 1 && api.undoOne() === n0 - 2, 'undoOne rewinds one move at a time');

  // ★研究モードを通しても対局経路が変わらない(先後エントリが戻る)
  setup(0);
  api.analyzePly(8, 3, 1, 0);      // 白番の局面を解析 → sec = true
  api.analyze();                   // 対局経路。sec は humanIsBlack(= false)に戻るはず
  const mixed = api.lastScore();
  setup(0);
  api.analyze();
  check(mixed === api.lastScore(), `game path is unaffected by research mode (${mixed})`);
}
api.newGame(1, 3);

console.log('\n=== speed (AI vs AI full game per model x profile) ===');
const want = process.argv.slice(2).map(Number);
const ids = want.length ? want : [0, 1, 2, 3];
console.log('model           id  name        plies            moves   total_s    max_ms    avg_ms          nodes');
console.log('------------------------------------------------------------------------------------------------------');
for (let mdl = 0; mdl < api.modelNum(); mdl++) {
  if (api.modelAvail(mdl) !== 1) { console.log(`${api.modelName(mdl)}: unavailable (weights not loaded)`); continue; }
  api.setModel(mdl);
  for (const i of ids) {
    api.seed(SEED);          // 上のテストの実行順に左右されないよう、1 局ごとに固定する
    api.newGame(0, i);
    let total = 0, mx = 0, nodes = 0, moves = 0, g = 0;
    while (api.status() === 0 && g++ < 70) {
      if (api.think() < 0) break;
      const ms = api.lastMs();
      total += ms; nodes += api.lastNodes(); if (ms > mx) mx = ms; moves++;
    }
    const plies = [0,1,2,3].map(b => api.profilePlies(i, b)).join('/');
    console.log(
      `${(api.modelName(mdl) + '/' + api.modelWeights(mdl)).padEnd(15)} ${String(i).padEnd(3)} ${api.profileName(i).padEnd(10)} ${plies.padEnd(15)} ` +
      `${String(moves).padStart(5)} ${(total/1000).toFixed(2).padStart(9)} ${mx.toFixed(0).padStart(9)} ` +
      `${(total/moves).toFixed(1).padStart(9)} ${nodes.toFixed(0).padStart(14)}`);
  }
}
api.setModel(0);

console.log(`\n==== ${fail === 0 ? 'ALL PASS' : 'FAILED'} (${fail} failures) ====`);
process.exit(fail === 0 ? 0 : 1);
