// 探索エンジン(WASM)を動かす Web Worker。
// 1 手の思考が数百 ms〜数十秒ブロックするため、必ずメインスレッドから分離する。
//   設計: docs/設計書/Web公開/implementation-plan-web-ui-3d.md §5
import YonmokuModule from './yonmoku.js';

let M = null;
let api = null;
let handPtr = 0;

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
  };
  api.init();
  handPtr = M._malloc(64 * 2 * 4);

  const profiles = [];
  for (let i = 0; i < api.profileNum(); i++) {
    profiles.push({
      id: i,
      name: api.profileName(i),
      plies: [0, 1, 2, 3].map((b) => api.profilePlies(i, b)),
    });
  }
  post({ type: 'ready', profiles, defaultProfile: api.profileDef() });
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
    profile: api.profileCur(),
    moveCount: api.moveCount(),
    evalValid: api.lastValid() === 1,
    scoreBlack: api.lastScore(),
    winRateBlack: api.winRate(),
    isMate: api.lastIsMate() === 1,
    lastMs: api.lastMs(),
    lastNodes: api.lastNodes(),
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
      api.newGame(m.humanIsBlack ? 1 : 0, m.profile);
      post(state());
      break;
    case 'setProfile':
      api.setProfile(m.profile);
      post(state());
      break;
    case 'play': {
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
    default:
      break;
  }
};
