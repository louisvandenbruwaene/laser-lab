// Laser Lab level generator: plants a solution on a random bench, then proves with an exhaustive solver that
// it is the only way to light the targets with that few pieces. Crystals are added where other routes run until
// the planted one is the unique shortest solution.
//   node laser/levelgen.mjs <seed> <tier 0..1> <count>   -> prints one level JSON per line
import fs from 'fs';
const html = fs.readFileSync(new URL('./index.html', import.meta.url), 'utf8');
const sim = html.match(/<script id="sim">([\s\S]*?)<\/script>/)[1];
const { build, trace, solved, PRISM, SL, BS, DX, DY } =
  new Function(sim + ';return {build,trace,solved,PRISM,SL,BS,DX,DY};')();

/* ---------- solver: follow the beams, decide each free square the first time light reaches it ---------- */
// A shortest solution never has an unlit piece, so deciding a square when a beam first enters it enumerates
// every lit configuration exactly once. Light only ever adds up, so a lit crystal or a wrong colour on a target
// is a dead end straight away.
export function solve(L, budget, maxNodes = 4e6, keep = 40, stopAt = Infinity) {
  const B = build(L), { w, h, n, tile, col, gid, need, fixed } = B;
  const plc = new Uint8Array(n);
  for (let i = 0; i < n; i++) plc[i] = tile[i] === 0 && !fixed[i] ? 1 : 0;
  const tray = { m: L.tray.m || 0, s: L.tray.s || 0, p: L.tray.p || 0 };
  const tgs = L.tg.map(([x, y]) => y * w + x);
  let best = budget, nb = 0, sols = [], found = [], nodes = 0, aborted = false, enough = false;
  const st0 = { dec: new Int8Array(n).fill(-1), hit: new Uint8Array(n), seen: new Uint16Array(n), open: 0,
    relay: new Uint8Array(n), stack: [], pend: [], m: 0, s: 0, p: 0, k: 0 };
  for (const [x, y, d, c] of L.em) st0.stack.push(x, y, d, c);
  const clone = s => ({ dec: s.dec.slice(), hit: s.hit.slice(), seen: s.seen.slice(), open: s.open,
    relay: s.relay.slice(), stack: s.stack.slice(), pend: s.pend.slice(), m: s.m, s: s.s, p: s.p, k: s.k });
  function advance(st) {
    const S = st.stack;
    while (S.length) {
      let c = S.pop(), d = S.pop(), y = S.pop(), x = S.pop();
      for (;;) {
        const nx = x + DX[d], ny = y + DY[d];
        if (nx < 0 || ny < 0 || nx >= w || ny >= h) break;
        const i = ny * w + nx, t = tile[i];
        if (t === 1 || t === 3 || t === 4 || t === 5 || t === 6 || t === 9 || (t === 10 && !(st.open >> gid[i] & 1)) || (t === 7 && col[i] !== c)) {
          st.hit[i] |= 1 << c;
          if (t === 5) return -2;
          if (t === 4 && (1 << c) & ~need[i]) return -2;
          if (t === 10) st.pend.push(x, y, d, c, gid[i]);
          else if (t === 6 && col[i] === c && !st.relay[i]) { st.relay[i] = 1; for (let e = 0; e < 4; e++) S.push(nx, ny, e, c); }
          else if (t === 9 && col[i] === c && !(st.open >> gid[i] & 1)) {
            st.open |= 1 << gid[i];
            const P = st.pend; st.pend = [];
            for (let j = 0; j < P.length; j += 5) if (P[j + 4] === gid[i]) S.push(P[j], P[j + 1], P[j + 2], P[j + 3]); else st.pend.push(P[j], P[j + 1], P[j + 2], P[j + 3], P[j + 4]);
          }
          break;
        }
        if (plc[i] && st.dec[i] < 0) { S.push(x, y, d, c); return i; }
        const bit = 1 << (d * 3 + c);
        if (st.seen[i] & bit) break;
        st.seen[i] |= bit; st.hit[i] |= 1 << c; x = nx; y = ny;
        if (t === 8) c = col[i]; else if (t === 11) d = PRISM(d, c, col[i]);
        const p = fixed[i] || (st.dec[i] > 0 ? st.dec[i] : 0);
        if (p === 1) d = SL[d]; else if (p === 2) d = BS[d];
        else if (p === 3) S.push(x, y, SL[d], c); else if (p === 4) S.push(x, y, BS[d], c);
        else if (p >= 5) d = PRISM(d, c, p - 5);
      }
    }
    return -1;
  }
  // Lower bound: light already traced is final, so every colour a target still lacks must come from a live beam
  // head. Relaxed search from those heads: straight on is free, a turn on an undecided square costs one piece.
  // If some missing colour is further than the pieces left, prune.
  const QM = 65535, dq = new Int32Array(QM + 1), dist = new Uint8Array(n * 12), stamp = new Uint32Array(n * 12), got = new Uint8Array(n);
  let epoch = 0;
  function feasible(st, r) {
    let missing = false;
    for (const i of tgs) if (need[i] & ~st.hit[i]) { missing = true; break; }
    if (!missing) return true;
    epoch++; got.fill(0);
    // 0-1 BFS on a ring deque: free moves go to the front, turns to the back
    let qf = 0, qb = 0;
    const relax = (j, d, c, k) => { const s = (j * 4 + d) * 3 + c; if (stamp[s] === epoch && dist[s] <= k) return; stamp[s] = epoch; dist[s] = k;
      if (k === kc) { qf = qf - 1 & QM; dq[qf] = s; } else { dq[qb] = s; qb = qb + 1 & QM; } };
    let kc = 0;
    const S = st.stack, Pd = st.pend;
    for (let j = 0; j < S.length; j += 4) relax(S[j + 1] * w + S[j], S[j + 2], S[j + 3], 0);
    for (let j = 0; j < Pd.length; j += 5) relax(Pd[j + 1] * w + Pd[j], Pd[j + 2], Pd[j + 3], 0);
    {
      while (qf !== qb) {
        const s = dq[qf]; qf = qf + 1 & QM; const k = dist[s]; if (k > r) continue; kc = k;
        const c0 = s % 3, d = (s / 3 | 0) % 4, i = s / 12 | 0, x = i % w + DX[d], y = (i / w | 0) + DY[d];
        if (x < 0 || y < 0 || x >= w || y >= h) continue;
        const j = y * w + x, t = tile[j];
        if (t === 1 || t === 3 || t === 5 || t === 9 || (t === 7 && col[j] !== c0)) continue;
        if (t === 4) { got[j] |= 1 << c0; continue; }
        if (t === 6) { if (col[j] === c0) for (let e = 0; e < 4; e++) relax(j, e, c0, k); continue; }
        const c = t === 8 ? col[j] : c0, d2 = t === 11 ? PRISM(d, c, col[j]) : d;
        const p = fixed[j] || (st.dec[j] > 0 ? st.dec[j] : 0);
        if (p === 1) relax(j, SL[d2], c, k); else if (p === 2) relax(j, BS[d2], c, k);
        else if (p === 3) { relax(j, d2, c, k); relax(j, SL[d2], c, k); }
        else if (p === 4) { relax(j, d2, c, k); relax(j, BS[d2], c, k); }
        else if (p >= 5) relax(j, PRISM(d2, c, p - 5), c, k);
        else { relax(j, d2, c, k); if (plc[j] && st.dec[j] < 0 && k < r) { relax(j, (d2 + 1) % 4, c, k + 1); relax(j, (d2 + 3) % 4, c, k + 1); } }
      }
    }
    for (const i of tgs) if (need[i] & ~st.hit[i] & ~got[i]) return false;
    return true;
  }
  function rec(st) {
    if (++nodes > maxNodes) { aborted = true; return; }
    const r = advance(st);
    if (r === -2) return;
    if (r >= 0 && !feasible(st, best - st.k)) return;
    if (r === -1) {
      for (const i of tgs) if (st.hit[i] !== need[i]) return;
      if (st.k < best) { best = st.k; nb = 0; sols = []; }
      nb++; if (sols.length < keep) sols.push(st.dec.slice());
      if (found.length < keep) found.push(st.dec.slice());
      if (found.length >= stopAt) { enough = aborted = true; }
      return;
    }
    const opts = [0];
    if (st.k < best) {
      if (st.m < tray.m) opts.push(1, 2);
      if (st.s < tray.s) opts.push(3, 4);
      if (st.p < tray.p) opts.push(5, 6, 7, 8);
    }
    for (let j = opts.length - 1; j >= 0; j--) {
      const o = opts[j];
      if (o && st.k >= best) continue;     // best may have dropped while exploring siblings
      const s2 = j ? clone(st) : st;
      s2.dec[r] = o;
      if (o) { s2.k++; if (o <= 2) s2.m++; else if (o <= 4) s2.s++; else s2.p++; }
      rec(s2);
      if (aborted) return;
    }
  }
  rec(st0);
  const toPieces = dec => { const P = new Uint8Array(n); dec.forEach((v, i) => { if (v > 0) P[i] = v; }); return P; };
  return { best: nb ? best : Infinity, count: nb, sols: sols.map(toPieces), found: found.map(toPieces), nodes, aborted, enough };
}

/* ---------- generator ---------- */
const FC = {}, F = k => { FC[k] = (FC[k] || 0) + 1; return null; };
let seed = 1;
const rnd = () => { seed = seed + 0x6D2B79F5 | 0; let z = Math.imul(seed ^ seed >>> 15, 1 | seed); z = z + Math.imul(z ^ z >>> 7, 61 | z) ^ z; return ((z ^ z >>> 14) >>> 0) / 4294967296; };
const ri = n => Math.floor(rnd() * n);
const pick = a => a[ri(a.length)];
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = ri(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; };

function lerp(a, b, t) { return a + (b - a) * t; }
function params(t) {
  return {
    w: Math.round(lerp(11, 14, t)), h: Math.round(lerp(8, 10, t)),
    kmin: Math.round(lerp(6, 9, t)), K: Math.round(lerp(6, 9, t)) + 1 + ri(2),
    nEm: Math.min(4, 2 + ri(2) + (t > .5 ? 1 : 0)),
    nTg: 3 + ri(2) + (t > .6 ? 1 : 0),
    walls: lerp(.09, .13, t), grates: lerp(.04, .18, t),
    prisms: rnd() < .35 + .4 * t, nPr: ri(2) + (t > .5 ? 1 : 0), nCs: ri(2) + (t > .4 ? ri(2) : 0),
    relay: rnd() < .3 + .4 * t, gate: rnd() < .3 + .5 * t, nGl: ri(2) + (t > .5 ? 1 : 0), nFx: ri(2),
    spare: t < .3 ? 0 : ri(2), decoys: 2 + ri(3),
  };
}

function attempt(t) {
  const P = params(t), { w, h, K } = P, n = w * h;
  const grid = Array.from({ length: h }, () => Array(w).fill('.'));
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const r = rnd(); if (r < P.walls) grid[y][x] = '#'; else if (r < P.walls + P.grates) grid[y][x] = ':';
  }
  const L = { name: '', w, h, map: [], em: [], tg: [], cr: [], fx: [], tray: { m: 0, s: 0 }, par: K, sol: [] };
  const occ = new Set();
  const free = () => { for (let k = 0; k < 200; k++) { const x = ri(w), y = ri(h); if (grid[y][x] === '.' && !occ.has(y * w + x)) return [x, y]; } return F(0); };
  const cols = shuffle([0, 1, 2]);
  for (let e = 0; e < P.nEm; e++) {
    const f = free(); if (!f) return F(1); const [x, y] = f;
    const dirs = [0, 1, 2, 3].filter(d => { const nx = x + DX[d], ny = y + DY[d]; return nx >= 0 && ny >= 0 && nx < w && ny < h && grid[ny][nx] !== '#'; });
    if (!dirs.length) return F(2);
    L.em.push([x, y, pick(dirs), cols[e % 3]]); occ.add(y * w + x);
  }
  if (P.nPr) L.pr = []; if (P.nCs) L.cs = [];
  for (let k = 0; k < P.nPr; k++) { const f = free(); if (f) { L.pr.push([...f, ri(4)]); occ.add(f[1] * w + f[0]); } }
  for (let k = 0; k < P.nCs; k++) { const f = free(); if (f) { L.cs.push([...f, ri(3)]); occ.add(f[1] * w + f[0]); } }
  for (let k = 0; k < P.nFx; k++) { const f = free(); if (f) { L.fx.push([...f, 1 + ri(2)]); occ.add(f[1] * w + f[0]); } }
  L.map = grid.map(r => r.join(''));
  // plant: wander the beams, dropping pieces now and then
  const kinds = []; for (let k = 0; k < K; k++) kinds.push(P.prisms && rnd() < .2 ? 'p' : rnd() < .3 ? 's' : 'm');
  const cnt = { m: 0, s: 0, p: 0 }; for (const k of kinds) cnt[k]++;
  L.tray = { m: cnt.m, s: cnt.s }; if (cnt.p) L.tray.p = cnt.p;
  let B = build(L);
  const pieces = new Uint8Array(n), decided = new Uint8Array(n);
  let placed = 0, q = .25 + rnd() * .25;
  for (let guard = 0; guard < 400 && placed < K; guard++) {
    const r = trace(B, pieces, false);
    const cand = []; for (let i = 0; i < n; i++) if (r.seen[i] && !decided[i] && B.tile[i] === 0 && !B.fixed[i] && !pieces[i]) cand.push(i);
    if (!cand.length) break;
    const i = pick(cand); decided[i] = 1;
    if (rnd() < Math.min(.6, q * 6 * (K - placed) / cand.length)) { const k = kinds[placed]; pieces[i] = k === 'm' ? 1 + ri(2) : k === 's' ? 3 + ri(2) : 5 + ri(4); placed++; }
  }
  if (placed < K) return F(3);
  // drop prisms and shifters no beam reaches
  let r = trace(B, pieces, false);
  if (L.pr) L.pr = L.pr.filter(([x, y]) => r.seen[y * w + x]);
  if (L.cs) L.cs = L.cs.filter(([x, y]) => r.seen[y * w + x]);
  L.fx = L.fx.filter(([x, y]) => r.seen[y * w + x]);
  if (L.pr && !L.pr.length) delete L.pr; if (L.cs && !L.cs.length) delete L.cs;
  B = build(L);
  const termini = () => {
    const r = trace(B, pieces, true), out = new Map();
    for (let j = 0; j < r.segs.length; j += 5) if (r.segs[j + 4] < 1) {
      const x = r.segs[j], y = r.segs[j + 1], i = y * w + x;
      if (B.tile[i] === 0 && !B.fixed[i] && !pieces[i]) out.set(i, (out.get(i) || 0) | 1 << r.segs[j + 3]);
    }
    return { r, out: [...out] };
  };
  // relay at a beam's end, then a switch at another end with a gate somewhere on the light
  if (P.relay) {
    const { out } = termini(); const c = out.filter(([, m]) => !(m & (m - 1)));
    if (c.length) { const [i, m] = pick(c); L.rl = [[i % w, i / w | 0, Math.log2(m)]]; B = build(L); }
  }
  if (P.gate) {
    const { r, out } = termini(); const c = out.filter(([, m]) => !(m & (m - 1)));
    const lit = []; for (let i = 0; i < n; i++) if (r.seen[i] && B.tile[i] === 0 && !B.fixed[i] && !pieces[i]) lit.push(i);
    if (c.length && lit.length > 4) {
      const [si, m] = pick(c); L.sw = [[si % w, si / w | 0, Math.log2(m), 1]];
      const gi = pick(lit.filter(i => i !== si)); L.gt = [[gi % w, gi / w | 0, 1]];
      B = build(L);
      const r2 = trace(B, pieces, false);
      if (!r2.open.has(1) || !r2.seen[gi]) { delete L.sw; delete L.gt; B = build(L); }
    }
  }
  // targets at beam ends and crossings
  r = trace(B, pieces, false);
  const ends = termini().out.map(([i]) => i);
  const cross = []; for (let i = 0; i < n; i++) if (B.tile[i] === 0 && !B.fixed[i] && !pieces[i] && r.hit[i] & (r.hit[i] - 1)) cross.push(i);
  const tcand = shuffle([...new Set([...shuffle(cross).slice(0, 2), ...shuffle(ends)])]);
  if (tcand.length < P.nTg) return F(4);
  L.tg = tcand.slice(0, P.nTg).map(i => [i % w, i / w | 0, 0]);
  for (let it = 0; it < 4; it++) {
    B = build(L); r = trace(B, pieces, false);
    L.tg = L.tg.map(([x, y]) => [x, y, r.hit[y * w + x]]).filter(t => t[2]);
  }
  B = build(L); r = trace(B, pieces, false);
  if (L.tg.length < 3 || !solved(B, r.hit)) return F(5);
  if (L.rl && !r.relayOn[L.rl[0][1] * w + L.rl[0][0]]) return F(6);
  if (L.gt && !r.open.has(1)) return F(7);
  // glass on squares one colour crosses
  const one = []; for (let i = 0; i < n; i++) if (B.tile[i] === 0 && !B.fixed[i] && !pieces[i] && r.hit[i] && !(r.hit[i] & (r.hit[i] - 1))) one.push(i);
  if (P.nGl) L.gl = shuffle(one).slice(0, P.nGl).map(i => [i % w, i / w | 0, Math.log2(r.hit[i])]);
  // every piece pulls its weight
  B = build(L);
  for (let i = 0; i < n; i++) if (pieces[i]) {
    const p = pieces[i]; pieces[i] = 0; const ok = solved(B, trace(B, pieces, false).hit); pieces[i] = p; if (ok) return F(8);
  }
  if (!r.seen || !solved(B, trace(B, pieces, false).hit)) return F(9);
  // decoy crystals next to the light
  const lit = trace(B, pieces, false).hit;
  const near = []; for (let i = 0; i < n; i++) if (B.tile[i] === 0 && !B.fixed[i] && !lit[i]) {
    const x = i % w, y = i / w | 0; if ([0, 1, 2, 3].some(d => { const X = x + DX[d], Y = y + DY[d]; return X >= 0 && Y >= 0 && X < w && Y < h && lit[Y * w + X]; })) near.push(i);
  }
  L.cr = shuffle(near).slice(0, P.decoys).map(i => [i % w, i / w | 0]);
  // spare pieces
  L.spare = {};
  for (let k = 0; k < P.spare; k++) { const kk = rnd() < .6 ? 'm' : 's'; L.tray[kk] = (L.tray[kk] || 0) + 1; L.spare[kk] = (L.spare[kk] || 0) + 1; }
  L.sol = []; for (let i = 0; i < n; i++) if (pieces[i]) L.sol.push([i % w, i / w | 0, pieces[i]]);
  return { L, pieces, kmin: P.kmin };
}

// Carve away every other shortest route until one is left. A shorter route that still needs at least kmin pieces
// becomes the reference instead; others die by a crystal on a square only they light, or a grate on a square
// only they put a piece on.
function refine(L, ref, kmin, maxNodes) {
  const w = L.w, n = L.w * L.h, key = P => P.join();
  const count = P => P.reduce((a, p) => a + (p ? 1 : 0), 0);
  for (let round = 0; round < 30; round++) {
    const B = build(L), refHit = trace(B, ref, false).hit;
    const t0 = Date.now();
    const res = solve(L, L.par, maxNodes, 60, 24);
    if (process.env.DEBUG) console.error('  round', round, 'par', L.par, 'nodes', res.nodes, 'ms', Date.now() - t0, 'found', res.found.length, 'count', res.count, 'best', res.best, 'aborted', res.aborted, 'cr', L.cr.length);
    if (res.aborted && !res.enough) return F(10);
    if (!res.aborted && res.best === L.par && res.count === 1) {
      L.sol = []; for (let i = 0; i < n; i++) if (ref[i]) L.sol.push([i % w, i / w | 0, ref[i]]);
      return { L, nodes: res.nodes };
    }
    const rk = key(ref);
    const alts = res.found.filter(s => key(s) !== rk);
    if (!alts.length) return F(11);
    const short = alts.filter(s => count(s) < L.par && count(s) >= kmin).sort((a, b) => count(a) - count(b));
    if (short.length) {
      ref = short[0]; L.par = count(ref);
      const use = { m: 0, s: 0, p: 0 }; for (const p of ref) if (p) use[p <= 2 ? 'm' : p <= 4 ? 's' : 'p']++;
      for (const k of ['m', 's', 'p']) { const v = use[k] + (L.spare[k] || 0); if (v) L.tray[k] = v; else if (k === 'p') delete L.tray.p; else L.tray[k] = 0; }
      continue;
    }
    // greedy cover of the alternatives
    const left = alts.map(s => ({ s, hit: trace(B, s, false).hit }));
    for (let add = 0; add < 4 && left.length; add++) {
      const score = new Map();
      const bump = (key, v) => score.set(key, (score.get(key) || 0) + v);
      for (const { s, hit } of left) for (let i = 0; i < n; i++) {
        if (B.tile[i] !== 0 || B.fixed[i]) continue;
        if (hit[i] && !refHit[i] && L.cr.length < 16) bump('c' + i, 1.3);
        if (s[i] && !ref[i]) bump('g' + i, 1);
      }
      if (!score.size) { if (add === 0) return F(12); break; }
      const top = Math.max(...score.values());
      const mv = pick([...score].filter(([, v]) => v === top))[0], i = +mv.slice(1);
      if (mv[0] === 'c') L.cr.push([i % w, i / w | 0]);
      else { const y = i / w | 0, x = i % w; L.map[y] = L.map[y].slice(0, x) + ':' + L.map[y].slice(x + 1); }
      B.tile[i] = 2;    // keep later picks in this round off the square
      for (let j = left.length - 1; j >= 0; j--) if (mv[0] === 'c' ? left[j].hit[i] : left[j].s[i]) left.splice(j, 1);
    }
  }
  return F(14);
}

const [, , seedArg = '1', tierArg = '0.5', countArg = '1', nodesArg = '3000000'] = process.argv;
if (import.meta.url === `file://${process.argv[1]}`) {
  seed = +seedArg; const t = +tierArg;
  let made = 0;
  for (let a = 0; made < +countArg && a < 100000; a++) {
    if (process.env.DEBUG && a % 5000 === 0) console.error(a, JSON.stringify(FC));
    const g = attempt(t); if (!g) continue;
    const t0 = Date.now(), out = refine(g.L, g.pieces, g.kmin, +nodesArg);
    if (!out) continue;
    const L = out.L;
    // final check against the game's own beam code
    const B = build(L), P = new Uint8Array(B.n);
    for (const [x, y, p] of L.sol) P[y * L.w + x] = p;
    if (!solved(B, trace(B, P, false).hit)) continue;
    delete L.spare;
    console.log(JSON.stringify({ ...L, nodes: out.nodes, ms: Date.now() - t0 }));
    made++;
  }
}
