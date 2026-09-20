// 探索エンジン(WASM)を動かす Web Worker。
// 1 手の思考が数百 ms〜数十秒ブロックするため、必ずメインスレッドから分離する。
//   設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §5
import YonmokuModule from './yonmoku.js';

let M = null;
let api = null;
let handPtr = 0;
let schedTurnPtr = 0;   // yon_set_schedule 用(最大 8 行 × int)
let schedPlyPtr = 0;

// ★i64 の戻り値は符号付き BigInt。bit63(マス 3,3,3)が立つと負値になるので必ず符号を落とす。
const u64 = (v) => BigInt.asUintN(64, v);

// ビットボード → マス番号の配列(描画側が扱いやすい形)
function cells(v) {
  const x = u64(v);
  const out = [];
  for (let k = 0; k < 64; k++) if ((x >> BigInt(k)) & 1n) out.push(k);
  return out;
}

async function boot() {
  M = await YonmokuModule();
  const c = (n, r, a) => M.cwrap(n, r, a);
  api = {
    init:         c('yon_init', null, []),
    newGame:      c('yon_new_game', null, ['number', 'number']),
    setProfile:   c('yon_set_profile', null, ['number']),
    play:         c('yon_play', 'number', ['number', 'number']),
    think:        c('yon_think', 'number', []),
    analyze:      c('yon_analyze', 'number', []),
    undo:         c('yon_undo', 'number', []),
    legal:        c('yon_legal_columns', 'number', []),
    landingZ:     c('yon_landing_z', 'number', ['number', 'number']),
    status:       c('yon_status', 'number', []),
    turn:         c('yon_turn', 'number', []),
    moveCount:    c('yon_move_count', 'number', []),
    blackToMove:  c('yon_black_to_move', 'number', []),
    humanIsBlack: c('yon_human_is_black', 'number', []),
    lastPlayedSq: c('yon_last_played_sq', 'number', []),
    lastScore:    c('yon_last_score', 'number', []),
    lastValid:    c('yon_last_valid', 'number', []),
    lastIsMate:   c('yon_last_is_mate', 'number', []),
    lastMs:       c('yon_last_ms', 'number', []),
    lastNodes:    c('yon_last_nodes', 'number', []),
    winRate:      c('yon_win_rate_black', 'number', []),
    hand:         c('yon_hand', 'number', ['number']),
    profileNum:   c('yon_profile_num', 'number', []),
    profileDef:   c('yon_profile_default', 'number', []),
    profileCur:   c('yon_profile_current', 'number', []),
    profileName:  c('yon_profile_name', 'string', ['number']),
    profilePlies: c('yon_profile_plies', 'number', ['number', 'number']),
    profileTurn:  c('yon_profile_turn', 'number', ['number']),
    setModel:     c('yon_set_model', 'number', ['number']),
    modelNum:     c('yon_model_num', 'number', []),
    modelCur:     c('yon_model_current', 'number', []),
    modelName:    c('yon_model_name', 'string', ['number']),
    modelWeights: c('yon_model_weights', 'string', ['number']),
    modelAvail:   c('yon_model_available', 'number', ['number']),
    modelDef:     c('yon_model_default', 'number', []),
    setSchedule:  c('yon_set_schedule', 'number', ['number', 'number', 'number']),
    schedLen:     c('yon_schedule_len', 'number', []),
    schedTurn:    c('yon_schedule_turn', 'number', ['number']),
    schedPly:     c('yon_schedule_ply', 'number', ['number']),
    schedMaxRows: c('yon_schedule_max_rows', 'number', []),
    schedMaxPly:  c('yon_schedule_max_ply', 'number', []),
    schedMinPly:  c('yon_schedule_min_ply', 'number', []),
    currentPly:   c('yon_current_ply', 'number', []),
    // --- 研究モード ---
    setSeed:      c('yon_set_seed', null, ['number']),
    undoOne:      c('yon_undo_one', 'number', []),
    analyzePly:   c('yon_analyze_ply', 'number', ['number', 'number', 'number', 'number']),
    anaPly:       c('yon_ana_ply', 'number', []),
    anaCount:     c('yon_ana_count', 'number', []),
    anaSq:        c('yon_ana_sq', 'number', ['number']),
    anaScore:     c('yon_ana_score', 'number', ['number']),
    anaWinrate:   c('yon_ana_winrate', 'number', ['number']),
    anaTied:      c('yon_ana_tied', 'number', []),
    anaForced:    c('yon_ana_forced', 'number', []),
    anaComplete:  c('yon_ana_complete', 'number', []),
    anaMs:        c('yon_ana_ms', 'number', []),
    anaNodes:     c('yon_ana_nodes', 'number', []),
    anaRootMoves: c('yon_ana_root_moves', 'number', []),
    anaMaxK:      c('yon_ana_max_k', 'number', []),
    anaMaxPly:    c('yon_ana_max_ply', 'number', []),
  };
  api.init();
  handPtr = M._malloc(64 * 2 * 4);
  const maxRows = api.schedMaxRows();
  schedTurnPtr = M._malloc(maxRows * 4);
  schedPlyPtr = M._malloc(maxRows * 4);

  const profiles = [];
  for (let i = 0; i < api.profileNum(); i++) {
    profiles.push({
      id: i,
      name: api.profileName(i),
      plies: [0, 1, 2, 3].map((b) => api.profilePlies(i, b)),
      // プリセットを読み手数スケジュール(手数, 読み手数)の 4 行に開いたもの
      rows: [0, 1, 2, 3].map((b) => [api.profileTurn(b), api.profilePlies(i, b)]),
    });
  }
  const models = [];
  for (let i = 0; i < api.modelNum(); i++) {
    models.push({
      id: i,
      name: api.modelName(i),        // 探索エンジン名 "alpha" / "core"
      weights: api.modelWeights(i),  // 重みバージョン "ver7.2" / "ver8.2.5" など
      available: api.modelAvail(i) === 1,
    });
  }
  post({
    type: 'ready',
    profiles,
    models,
    defaultProfile: api.profileDef(),
    defaultModel: api.modelDef(),
    limits: {
      maxRows, maxPly: api.schedMaxPly(), minPly: api.schedMinPly(),
      anaMaxK: api.anaMaxK(), anaMaxPly: api.anaMaxPly(),
    },
  });
}

// ===== 研究モード: 反復深化の外側ループ =====
// ★WASM の探索は同期実行で Worker を完全にブロックする。for で回すと全反復が終わるまで
//   postMessage が 1 通も届かない。1 反復 = 1 タスクに切り出し、反復ごとに setTimeout で
//   キューへ戻す。これで結果が逐次届き、間に入った analyzeStop も処理される。
//   設計: docs/設計書/Web公開/implementation-plan-research-analysis.md §4.3
const SOLVED = 1e8;   // |評価値| がこれ以上なら勝敗を読み切っている

let ana = null;   // { ply, topK, freshTt, deadlineMs, stop }

function anaEnd(reason) {
  ana = null;
  post({ type: 'analyzeEnd', reason });
}

function anaStep() {
  if (!ana) return;
  if (ana.stop) return anaEnd('stopped');

  // 空きマス数を超える読みは全読みと同じ。それ以上深めても値は変わらない
  const empty = 64 - api.moveCount();
  if (ana.ply > empty) return anaEnd('exhausted');

  const r = api.analyzePly(ana.ply, ana.topK, ana.freshTt ? 1 : 0, ana.deadlineMs);
  if (r < 0) return anaEnd('invalid');

  const moves = [];
  for (let i = 0; i < api.anaCount(); i++) {
    const s = api.anaScore(i);
    moves.push({
      sq: api.anaSq(i),
      scoreBlack: s,
      winRateBlack: api.anaWinrate(i),
      isSolved: Math.abs(s) >= SOLVED,
    });
  }
  post({
    type: 'analyzeIter',
    ply: ana.ply,
    complete: r === 1,
    forced: api.anaForced(),
    rootMoves: api.anaRootMoves(),
    tied: api.anaTied(),
    ms: api.anaMs(),
    nodes: api.anaNodes(),
    moves,
  });
  post(state());

  if (r === 0) return anaEnd('deadline');                       // 期限切れ(途中結果は送信済み)
  if (moves.length && moves[0].isSolved) return anaEnd('solved');
  if (api.anaForced() === 1) return anaEnd('solved');           // 即勝ち

  ana.ply += 2;
  setTimeout(anaStep, 0);   // ★ここでタスクキューへ戻す
}

// スケジュールを WASM に渡す。戻り値は yon_set_schedule のエラーコード(0 = OK)
function writeSchedule(rows) {
  for (let i = 0; i < rows.length; i++) {
    M.HEAP32[(schedTurnPtr >> 2) + i] = rows[i][0];
    M.HEAP32[(schedPlyPtr >> 2) + i] = rows[i][1];
  }
  return api.setSchedule(schedTurnPtr, schedPlyPtr, rows.length);
}

function readSchedule() {
  const out = [];
  for (let i = 0; i < api.schedLen(); i++) out.push([api.schedTurn(i), api.schedPly(i)]);
  return out;
}

function post(msg) { self.postMessage(msg); }

function readHand() {
  const n = api.hand(handPtr);
  const out = [];
  for (let i = 0; i < n; i++) out.push([M.HEAP32[(handPtr >> 2) + i * 2], M.HEAP32[(handPtr >> 2) + i * 2 + 1]]);
  return out;
}

// UI が必要とするすべてを 1 つにまとめて送る(UI は自前で盤面を持たない)
function state() {
  const landing = [];
  for (let y = 0; y < 4; y++) for (let x = 0; x < 4; x++) landing.push(api.landingZ(x, y));
  return {
    type: 'state',
    black: cells(M._yon_black()),
    white: cells(M._yon_white()),
    winLine: cells(M._yon_win_line()),
    turn: api.turn(),
    status: api.status(),
    legal: api.legal(),
    landing,
    lastSq: api.lastPlayedSq(),
    hand: readHand(),
    humanIsBlack: api.humanIsBlack() === 1,
    blackToMove: api.blackToMove() === 1,
    profile: api.profileCur(),        // -1 = カスタム(スケジュールを直接編集した)
    model: api.modelCur(),
    schedule: readSchedule(),
    currentPly: api.currentPly(),     // この局面で実際に使われる読み手数 N
    moveCount: api.moveCount(),
    evalValid: api.lastValid() === 1,
    scoreBlack: api.lastScore(),
    winRateBlack: api.winRate(),
    isMate: api.lastIsMate() === 1,
    lastMs: api.lastMs(),
    lastNodes: api.lastNodes(),
    anaPly: api.anaPly(),          // 研究モードで直前に解析した読み手数 N(対局中は 0)
    anaForced: api.anaForced(),
  };
}

self.onmessage = (e) => {
  const m = e.data;
  if (!api && m.type !== 'init') return;
  switch (m.type) {
    case 'init':
      boot().catch((err) => post({ type: 'error', message: String(err) }));
      break;
    case 'newGame':
      ana = null;
      api.newGame(m.humanIsBlack ? 1 : 0, m.profile);
      post(state());
      break;
    case 'setProfile':
      api.setProfile(m.profile);
      post(state());
      break;
    case 'setModel': {
      const r = api.setModel(m.model);
      post({ type: 'model', ok: r === 0, code: r });
      post(state());
      break;
    }
    case 'setSchedule': {
      const r = writeSchedule(m.rows);
      post({ type: 'schedule', ok: r === 0, code: r });
      post(state());
      break;
    }
    case 'play': {
      ana = null;                 // 局面が変わるので解析は打ち切る
      const r = api.play(m.x, m.y);
      post({ type: 'played', ok: r !== 2, sq: api.lastPlayedSq() });
      post(state());
      break;
    }
    case 'think': {
      post({ type: 'thinking' });
      const sq = api.think();
      post({
        type: 'moved',
        sq,
        scoreBlack: api.lastScore(),
        winRateBlack: api.winRate(),
        isMate: api.lastIsMate() === 1,
        ms: api.lastMs(),
        nodes: api.lastNodes(),
      });
      post(state());
      break;
    }
    case 'undo':
      api.undo();
      post(state());
      break;
    case 'undoOne':
      ana = null;               // 局面が変わるので解析は打ち切る
      api.undoOne();
      post(state());
      break;
    case 'analyzeStart':
      if (typeof m.seed === 'number') api.setSeed(m.seed);
      ana = {
        ply: m.startPly,
        topK: m.topK,
        freshTt: !!m.freshTt,
        deadlineMs: m.deadlineMs | 0,
        stop: false,
      };
      anaStep();
      break;
    case 'analyzeStop':
      if (ana) ana.stop = true;   // 実際に止まるのは走っている反復が終わったあと
      break;
    default:
      break;
  }
};
