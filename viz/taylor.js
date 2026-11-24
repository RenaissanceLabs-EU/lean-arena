// Real analysis: a function against its Taylor polynomial at 0. Inside the radius of convergence the
// error shrinks as the degree grows; outside it, the polynomials blow up.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, height: 4.6, pos: [0, 0, 10], controls: false });
  const X0 = -3, X1 = 3, YL = 2, NX = 600, NMAX = 15;
  const fact = [1]; for (let k = 1; k <= NMAX; k++) fact[k] = fact[k - 1] * k;
  const funcs = {
    sin: { name: 'sin x', f: Math.sin, c: (k) => (k % 2 ? ((k - 1) / 2 % 2 ? -1 : 1) / fact[k] : 0), R: Infinity },
    exp: { name: 'eˣ', f: Math.exp, c: (k) => 1 / fact[k], R: Infinity },
    rat: { name: '1 / (1 + x²)', f: (x) => 1 / (1 + x * x), c: (k) => (k % 2 ? 0 : (k / 2 % 2 ? -1 : 1)), R: 1 },
    ln: { name: 'ln(1 + x)', f: (x) => (x > -1 ? Math.log(1 + x) : NaN), c: (k) => (k === 0 ? 0 : (k % 2 ? 1 : -1) / k), R: 1 },
  };
  let key = 'sin', n = 5, pal = ctx.palette();
  const xs = new Float32Array(NX + 1), fv = new Float32Array(NX + 1), pv = new Float32Array(NX + 1);
  for (let i = 0; i <= NX; i++) xs[i] = X0 + (X1 - X0) * i / NX;

  function mkLines(max, color) {
    const g = new T.BufferGeometry(); const pos = new Float32Array(max * 6);
    g.setAttribute('position', new T.BufferAttribute(pos, 3)); g.setDrawRange(0, 0);
    const mat = new T.LineBasicMaterial({ color }); const obj = new T.LineSegments(g, mat); obj.frustumCulled = false; st.scene.add(obj);
    return { obj, mat, pos, g, n: 0 };
  }
  function seg(L, a, b, c, d) { const o = L.n * 6; L.pos[o] = a; L.pos[o + 1] = b; L.pos[o + 2] = 0; L.pos[o + 3] = c; L.pos[o + 4] = d; L.pos[o + 5] = 0; L.n++; }
  function flush(L) { L.g.setDrawRange(0, L.n * 2); L.g.attributes.position.needsUpdate = true; }
  const clampY = (y) => Math.max(-YL, Math.min(YL, y));
  function curve(L, ys) {
    L.n = 0;
    for (let i = 0; i < NX; i++) {
      const a = ys[i], b = ys[i + 1]; if (isNaN(a) || isNaN(b)) continue;
      if ((a > YL && b > YL) || (a < -YL && b < -YL)) continue;
      for (let k = 0; k < 2; k++) seg(L, xs[i], clampY(a) + k * 0.014, xs[i + 1], clampY(b) + k * 0.014);
    }
    flush(L);
  }
  const fLine = mkLines(NX * 2, pal.c2), pLine = mkLines(NX * 2, pal.c1);
  const grid = mkLines(80, pal.rule), frame = mkLines(8, pal.inkSoft), rad = mkLines(8, pal.c1);
  for (let k = -3; k <= 3; k++) seg(grid, k, -0.06, k, 0.06);
  for (let k = -2; k <= 2; k++) seg(grid, -0.06, k, 0.06, k);
  seg(grid, X0, 0, X1, 0); seg(grid, 0, -YL, 0, YL); flush(grid);
  seg(frame, X0, -YL, X1, -YL); seg(frame, X1, -YL, X1, YL); seg(frame, X1, YL, X0, YL); seg(frame, X0, YL, X0, -YL); flush(frame);

  // error band between f and the polynomial
  const bg = new T.BufferGeometry(); const bpos = new Float32Array((NX + 1) * 6); const bidx = new Uint32Array(NX * 6);
  bg.setAttribute('position', new T.BufferAttribute(bpos, 3)); bg.setIndex(new T.BufferAttribute(bidx, 1));
  const bmat = new T.MeshBasicMaterial({ transparent: true, opacity: 0.4, side: T.DoubleSide, depthWrite: false });
  const band = new T.Mesh(bg, bmat); band.frustumCulled = false; band.position.z = -0.1; st.scene.add(band);

  const labs = [];
  for (let k = -3; k <= 3; k++) { if (!k) continue; const l = ctx.label(String(k), { size: 0.22 }); l.position.set(k, -0.25, 1); st.scene.add(l); labs.push(l); }
  const lf = ctx.label('f(x)', { size: 0.3, bold: true }), lp = ctx.label('polynomial', { size: 0.3, bold: true }), le = ctx.label('error', { size: 0.3, bold: true });
  lf.position.set(-2.4, -1.7, 1); lp.position.set(-1.1, -1.7, 1); le.position.set(0.1, -1.7, 1); [lf, lp, le].forEach((l) => st.scene.add(l));
  const lr = ctx.label('|x| = 1', { size: 0.24 }); lr.position.set(1, 1.78, 1); st.scene.add(lr);

  const eWin = ctx.ui.readout({ label: 'Max error on [−3, 3]' }), eIn = ctx.ui.readout({ label: 'Max error on [−0.9, 0.9]' }), rOut = ctx.ui.readout({ label: 'Series converges for' });
  const fmt = (v) => (v > 1000 ? '> 1000' : v < 0.001 ? v.toExponential(1) : v.toPrecision(3));

  function recompute() {
    const F = funcs[key];
    for (let i = 0; i <= NX; i++) fv[i] = F.f(xs[i]);
    update();
  }
  function update() {
    const F = funcs[key]; const co = []; for (let k = 0; k <= n; k++) co.push(F.c(k));
    let mw = 0, mi = 0, vi = 0;
    for (let i = 0; i <= NX; i++) {
      const x = xs[i]; let s = 0; for (let k = n; k >= 0; k--) s = s * x + co[k]; pv[i] = s;
      if (!isNaN(fv[i])) { const e = Math.abs(fv[i] - s); if (e > mw) mw = e; if (Math.abs(x) <= 0.9 && e > mi) mi = e; }
    }
    curve(fLine, fv); curve(pLine, pv);
    let ni = 0;
    for (let i = 0; i <= NX; i++) {
      const ok = !isNaN(fv[i]); const a = ok ? clampY(fv[i]) : 0, b = ok ? clampY(pv[i]) : 0;
      bpos.set([xs[i], a, 0, xs[i], b, 0], i * 6);
      if (i < NX && ok && !isNaN(fv[i + 1])) { const j = i * 2; bidx.set([j, j + 1, j + 2, j + 1, j + 3, j + 2], ni); ni += 6; }
    }
    bg.setDrawRange(0, ni); bg.attributes.position.needsUpdate = true; bg.index.needsUpdate = true;
    eWin.set(fmt(mw)); eIn.set(fmt(mi));
    rOut.set(F.R === Infinity ? 'every x (R = ∞)' : '|x| < 1 (R = 1)');
    rad.n = 0; if (F.R === 1) { seg(rad, -1, -YL, -1, YL); seg(rad, 1, -YL, 1, YL); } flush(rad); lr.visible = F.R === 1;
    ctx.invalidate();
  }
  ctx.ui.select({ label: 'Function', options: Object.entries(funcs).map(([k, v]) => [k, v.name]), value: 'sin', onChange: (k) => { key = k; recompute(); } });
  ctx.ui.slider({ label: 'Degree n', min: 0, max: NMAX, step: 1, value: n, onInput: (v) => { n = v; update(); } });

  const fit = () => { const { w, h } = ctx.size(); st.camera.zoom = Math.min(1, (w / h * st.height) / 6.6); st.camera.updateProjectionMatrix(); ctx.invalidate(); };
  const ro = new ResizeObserver(fit); ro.observe(root); fit();
  ctx.onTheme((p) => {
    pal = p; fLine.mat.color.set(p.c2); pLine.mat.color.set(p.c1); bmat.color.set(p.c3); grid.mat.color.set(p.inkSoft); frame.mat.color.set(p.rule); rad.mat.color.set(p.c4);
    labs.forEach((l) => l.userData.setColor(p.inkSoft)); lf.userData.setColor(p.c2); lp.userData.setColor(p.c1); le.userData.setColor(p.c3); lr.userData.setColor(p.c4);
  });
  recompute();
  return { dispose() { ro.disconnect(); } };
}
