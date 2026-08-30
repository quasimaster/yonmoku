console.log('step1');
const mod = await import('./yonmoku.js');
console.log('step2 typeof=', typeof mod.default);
const M = await mod.default();
console.log('step3 ok, turn=', M._yon_turn(), 'profiles=', M._yon_profile_num());
