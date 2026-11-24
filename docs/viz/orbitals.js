// Quantum theory: hydrogen orbitals as clouds of electron positions drawn from |psi|^2 = R_nl(r)^2 Y(angles)^2 (lengths in Bohr radii a0).
const S2 = Math.SQRT2, S3 = Math.sqrt(3), S6 = Math.sqrt(6), S30 = Math.sqrt(30), E = Math.exp;
export const RADIAL = { // exact hydrogen radial functions, normalized so that the integral of r^2 R^2 dr is 1
  '10': (r) => 2 * E(-r),
  '20': (r) => (1 / (2 * S2)) * (2 - r) * E(-r / 2),
  '21': (r) => (1 / (2 * S6)) * r * E(-r / 2),
  '30': (r) => (2 / (81 * S3)) * (27 - 18 * r + 2 * r * r) * E(-r / 3),
  '31': (r) => (8 / (27 * S6)) * r * (1 - r / 6) * E(-r / 3),
  '32': (r) => (4 / (81 * S30)) * r * r * E(-r / 3),
};
// real angular shapes g(x,y,z) on the unit sphere, scaled so max |g| = 1 (the constant does not matter for sampling)
export const ORBITALS = [
  { k: '1s', name: '1s', n: 1, l: 0, g: () => 1 },
  { k: '2s', name: '2s', n: 2, l: 0, g: () => 1 },
  { k: '2p', name: '2p (z)', n: 2, l: 1, g: (x, y, z) => z },
  { k: '3s', name: '3s', n: 3, l: 0, g: () => 1 },
  { k: '3p', name: '3p (z)', n: 3, l: 1, g: (x, y, z) => z },
  { k: '3dz', name: '3d (z squared)', n: 3, l: 2, g: (x, y, z) => (3 * z * z - 1) / 2 },
  { k: '3dxy', name: '3d (xy)', n: 3, l: 2, g: (x, y) => 2 * x * y },
];
function rng(seed) { let a = seed >>> 0; return () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

// Radial part by inverse CDF of r^2 R^2, angular part by rejection on g^2; independent, so the product is exactly |psi|^2.
export function sampleOrbital(o, N, seed) {
  const R = RADIAL[o.n + '' + o.l], rmax = [0, 18, 45, 90][o.n], M = 4000, rand = rng(seed);
  const cdf = new Float64Array(M + 1); let mean = 0, norm = 0;
  for (let i = 1; i <= M; i++) {
    const r0 = (i - 1) * rmax / M, r1 = i * rmax / M, p0 = r0 * r0 * R(r0) ** 2, p1 = r1 * r1 * R(r1) ** 2, h = rmax / M;
    cdf[i] = cdf[i - 1] + 0.5 * (p0 + p1) * h; norm += 0.5 * (p0 + p1) * h; mean += 0.5 * (r0 * p0 + r1 * p1) * h;
  }
  const total = cdf[M], pos = new Float32Array(N * 3), sign = new Int8Array(N), rad = new Float32Array(N); let sum = 0;
  for (let s = 0; s < N; s++) {
    const u = rand() * total; let lo = 0, hi = M; while (hi - lo > 1) { const mid = (lo + hi) >> 1; if (cdf[mid] <= u) lo = mid; else hi = mid; }
    const r = (lo + (u - cdf[lo]) / Math.max(1e-300, cdf[hi] - cdf[lo])) * rmax / M;
    let x, y, z, g;
    for (;;) { z = 2 * rand() - 1; const ph = 2 * Math.PI * rand(), q = Math.sqrt(1 - z * z); x = q * Math.cos(ph); y = q * Math.sin(ph); g = o.g(x, y, z); if (rand() < g * g) break; }
    pos.set([r * x, r * z, r * y], s * 3); // z of the orbital points up on screen
    sign[s] = (R(r) * g >= 0) ? 1 : -1; rad[s] = r; sum += r;
  }
  const sorted = Float32Array.from(rad).sort();
  return { pos, sign, sampleMean: sum / N, exactMean: mean / total, norm, r99: sorted[Math.floor(0.99 * (N - 1))] };
}

export default function mount(root, ctx) {
  const T = ctx.THREE, NMAX = 20000;
  const st = ctx.stage({ pos: [4.4, 2.8, 6], fov: 40 });
  if (st.controls && !ctx.reduced) { st.controls.autoRotate = true; st.controls.autoRotateSpeed = 1.0; }
  const cache = {}; let cur = ORBITALS[0], count = 14000, cols = [new T.Color(), new T.Color()];
  const geo = new T.BufferGeometry();
  const posAttr = new T.BufferAttribute(new Float32Array(NMAX * 3), 3), colAttr = new T.BufferAttribute(new Float32Array(NMAX * 3), 3);
  geo.setAttribute('position', posAttr); geo.setAttribute('color', colAttr);
  const mat = new T.PointsMaterial({ size: 0.085, vertexColors: true, transparent: true, opacity: 0.9, depthWrite: false });
  const pts = new T.Points(geo, mat); pts.frustumCulled = false; st.scene.add(pts);
  // faint axes through the nucleus
  const ax = new T.LineSegments(new T.BufferGeometry().setFromPoints([[-3, 0, 0], [3, 0, 0], [0, -3, 0], [0, 3, 0], [0, 0, -3], [0, 0, 3]].map(v => new T.Vector3(...v))), new T.LineBasicMaterial({ transparent: true, opacity: 0.45 }));
  st.scene.add(ax);
  const lz = ctx.label('z', { size: 0.3 }), lx = ctx.label('x', { size: 0.3 }), ly = ctx.label('y', { size: 0.3 });
  lz.position.set(0, 3.2, 0); lx.position.set(3.2, 0, 0); ly.position.set(0, 0, 3.2); st.scene.add(lz, lx, ly);

  const outS = ctx.ui.readout({ label: 'Mean distance ⟨r⟩ of the dots / exact' }), outK = ctx.ui.readout({ label: 'Picture scale' });
  function face() { if (slice && st.controls) { st.camera.position.set(0, cur.k === '3dxy' ? 8.3 : 0, cur.k === '3dxy' ? 0.01 : 8.3); st.controls.update(); } }
  const sgn = new Int8Array(NMAX); let slice = false;
  function colorize() {
    const c = colAttr.array; for (let i = 0; i < NMAX; i++) { const k = cols[sgn[i] > 0 ? 0 : 1]; c[3 * i] = k.r; c[3 * i + 1] = k.g; c[3 * i + 2] = k.b; }
    colAttr.needsUpdate = true;
  }
  function show() {
    const d = cache[cur.k] || (cache[cur.k] = sampleOrbital(cur, NMAX, 1000 + ORBITALS.indexOf(cur)));
    let m = count;
    if (slice) { // keep only the dots within a thin slab around the plane y = 0, so shells and nodal planes show as gaps
      const lim = 0.1 * d.r99, ax2 = cur.k === '3dxy' ? 1 : 2; m = 0; const P = posAttr.array; // 3d(xy) is empty in the plane y = 0, so it is cut at z = 0 instead
      for (let i = 0; i < NMAX; i++) if (Math.abs(d.pos[3 * i + ax2]) < lim) { P[3 * m] = d.pos[3 * i]; P[3 * m + 1] = d.pos[3 * i + 1]; P[3 * m + 2] = d.pos[3 * i + 2]; sgn[m++] = d.sign[i]; }
    } else { posAttr.array.set(d.pos); sgn.set(d.sign); }
    posAttr.needsUpdate = true; colorize(); geo.setDrawRange(0, m);
    pts.scale.setScalar(2.4 / d.r99);
    let s = 0; for (let i = 0; i < count; i++) s += Math.hypot(d.pos[3 * i], d.pos[3 * i + 1], d.pos[3 * i + 2]);
    outS.set((s / count).toFixed(2) + ' a0  /  ' + d.exactMean.toFixed(2) + ' a0');
    outK.set((slice ? 'slice of thickness ' + (0.2 * d.r99).toFixed(1) + ' a0; ' : '') + '99% of the dots lie within ' + d.r99.toFixed(1) + ' a0');
    ctx.invalidate();
  }
  ctx.ui.select({ label: 'Orbital', options: ORBITALS.map(o => [o.k, o.name]), value: '1s', onChange: (k) => { cur = ORBITALS.find(o => o.k === k); face(); show(); } });
  ctx.ui.slider({ label: 'Number of dots', min: 8000, max: NMAX, step: 1000, value: count, onInput: (v) => { count = v; show(); } });
  ctx.ui.toggle({ label: 'Slice through the nucleus', value: false, onChange: (v) => {
    slice = v; if (st.controls) st.controls.autoRotate = !v && !ctx.reduced; face(); show();
  } });
  ctx.onTheme((p) => {
    cols[0].set(p.c2); cols[1].set(p.c3); ax.material.color.set(p.inkSoft);
    [lz, lx, ly].forEach(l => l.userData.setColor(p.inkSoft)); colorize();
  });
  show();
}
