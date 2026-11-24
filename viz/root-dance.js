// Polynomials: the roots of z^n - c (or z^5 - z - c) as the constant term c moves. Roots are tracked by
// continuation: Durand-Kerner iteration warm-started from the previous roots, with c moved in small substeps.
// A loop of c around the origin permutes the roots: the beginning of Galois theory.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 3.8, pos: [0, 0, 10] });
  const MAXD = 5, MAXT = 900, CMAX = 1.6;
  const polys = {
    cube: { name: 'z³ − c', n: 3, coef: (c) => [[-c[0], -c[1]], [0, 0], [0, 0], [1, 0]] },
    quad: { name: 'z⁴ − c', n: 4, coef: (c) => [[-c[0], -c[1]], [0, 0], [0, 0], [0, 0], [1, 0]] },
    quin: { name: 'z⁵ − z − c', n: 5, coef: (c) => [[-c[0], -c[1]], [-1, 0], [0, 0], [0, 0], [0, 0], [1, 0]] },
  };
  const C0 = [1.238, 0.847];
  let kind = 'cube', c = [...C0], zr = new Float64Array(MAXD), zi = new Float64Array(MAXD);
  const startR = new Float64Array(MAXD), startI = new Float64Array(MAXD);

  function evalP(co, x, y) { // Horner, ascending coefficients
    let pr = 0, pi = 0;
    for (let k = co.length - 1; k >= 0; k--) { const t = pr * x - pi * y + co[k][0]; pi = pr * y + pi * x + co[k][1]; pr = t; }
    return [pr, pi];
  }
  function dk(co, n, iters) { // Durand-Kerner, Gauss-Seidel style, in place on zr, zi
    for (let it = 0; it < iters; it++) {
      let md = 0;
      for (let i = 0; i < n; i++) {
        const [pr, pi] = evalP(co, zr[i], zi[i]); let dr = 1, di = 0;
        for (let j = 0; j < n; j++) if (j !== i) { const a = zr[i] - zr[j], b = zi[i] - zi[j]; const t = dr * a - di * b; di = dr * b + di * a; dr = t; }
        const q = dr * dr + di * di || 1e-300; const sr = (pr * dr + pi * di) / q, si = (pi * dr - pr * di) / q;
        zr[i] -= sr; zi[i] -= si; md = Math.max(md, Math.abs(sr) + Math.abs(si));
      }
      if (md < 1e-15) break;
    }
  }
  function residual(co, n) { let mx = 0; for (let i = 0; i < n; i++) { const [a, b] = evalP(co, zr[i], zi[i]); mx = Math.max(mx, Math.hypot(a, b)); } return mx; }
  function minSep(n) { let m = 1e9; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) m = Math.min(m, Math.hypot(zr[i] - zr[j], zi[i] - zi[j])); return m; }
  function fresh(co, n, prev) { // cold start, then match to previous roots by nearest neighbour (greedy)
    const pr = Float64Array.from(zr), pi = Float64Array.from(zi);
    for (let i = 0; i < n; i++) { const a = 0.4 + i * 1.3, r = 1.2; zr[i] = r * Math.cos(a); zi[i] = r * Math.sin(a) + 0.1; }
    dk(co, n, 500);
    if (!prev) return;
    const used = new Set(), nr = new Float64Array(n), ni = new Float64Array(n);
    for (let i = 0; i < n; i++) { let b = -1, bd = 1e9; for (let j = 0; j < n; j++) if (!used.has(j)) { const d = Math.hypot(zr[j] - pr[i], zi[j] - pi[i]); if (d < bd) { bd = d; b = j; } } used.add(b); nr[i] = zr[b]; ni[i] = zi[b]; }
    for (let i = 0; i < n; i++) { zr[i] = nr[i]; zi[i] = ni[i]; }
  }
  function solveAt(cx, cy, warm) {
    const P = polys[kind], co = P.coef([cx, cy]);
    if (warm) { const sr = Float64Array.from(zr), si = Float64Array.from(zi); dk(co, P.n, 60); if (residual(co, P.n) > 1e-9 || minSep(P.n) < 1e-7) { zr.set(sr); zi.set(si); fresh(co, P.n, true); } }
    else fresh(co, P.n, false);
    c = [cx, cy];
  }
  function moveTo(cx, cy) { // continuation: small substeps keep every root's identity
    const d = Math.hypot(cx - c[0], cy - c[1]), k = Math.max(1, Math.ceil(d / 0.02)), x0 = c[0], y0 = c[1];
    for (let s = 1; s <= k; s++) { solveAt(x0 + (cx - x0) * s / k, y0 + (cy - y0) * s / k, true); pushTrail(); }
    refresh();
  }

  // scene
  const cols = []; const dotMats = [], trailMats = [], dots = [], labels = [], trails = [], tcount = new Array(MAXD).fill(0), tbuf = [];
  const dg = new T.CircleGeometry(0.09, 24);
  for (let i = 0; i < MAXD; i++) {
    const dm = new T.MeshBasicMaterial(); const d = new T.Mesh(dg, dm); d.position.z = 0.3; st.scene.add(d); dots.push(d); dotMats.push(dm);
    const lb = ctx.label(String(i + 1), { size: 0.2, bold: true }); lb.position.z = 0.4; st.scene.add(lb); labels.push(lb);
    const buf = new Float32Array(MAXT * 3); tbuf.push(buf); const g = new T.BufferGeometry(); g.setAttribute('position', new T.BufferAttribute(buf, 3)); g.setDrawRange(0, 0);
    const tm = new T.LineBasicMaterial({ transparent: true, opacity: 0.8 }); const ln = new T.Line(g, tm); ln.frustumCulled = false; ln.position.z = 0.1; st.scene.add(ln); trails.push(ln); trailMats.push(tm);
  }
  const axPts = [-2.4, 0, 0, 2.4, 0, 0, 0, -2.4, 0, 0, 2.4, 0];
  const axMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.45 });
  st.scene.add(new T.LineSegments(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(axPts, 3)), axMat));
  const cirPts = []; for (let i = 0; i <= 128; i++) cirPts.push(Math.cos(i / 128 * 6.2832), Math.sin(i / 128 * 6.2832), 0);
  const cirMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.6 });
  const cir = new T.Line(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(cirPts, 3)), cirMat); st.scene.add(cir);
  const cMat = new T.MeshBasicMaterial(); const cMark = new T.Mesh(new T.RingGeometry(0.1, 0.17, 4), cMat); cMark.rotation.z = 0; cMark.position.z = 0.5; st.scene.add(cMark);
  const cLab = ctx.label('c', { size: 0.26, bold: true }); cLab.position.z = 0.5; st.scene.add(cLab);

  function pushTrail() {
    const n = polys[kind].n;
    for (let i = 0; i < n; i++) {
      const b = tbuf[i]; let k = tcount[i];
      if (k > 0 && Math.hypot(b[(k - 1) * 3] - zr[i], b[(k - 1) * 3 + 1] - zi[i]) < 0.004) continue;
      if (k >= MAXT) { b.copyWithin(0, 3, MAXT * 3); k = MAXT - 1; }
      b[k * 3] = zr[i]; b[k * 3 + 1] = zi[i]; b[k * 3 + 2] = 0; tcount[i] = k + 1;
      trails[i].geometry.setDrawRange(0, k + 1); trails[i].geometry.attributes.position.needsUpdate = true;
    }
  }
  function clearTrails() { for (let i = 0; i < MAXD; i++) { tcount[i] = 0; trails[i].geometry.setDrawRange(0, 0); } pushTrail(); }

  const cOut = ctx.ui.readout({ label: 'c' }), rOut = ctx.ui.readout({ label: 'max |p(root)|' }), pOut = ctx.ui.readout({ label: 'Root → old place of root' });
  function refresh() {
    const P = polys[kind], n = P.n;
    for (let i = 0; i < MAXD; i++) {
      const on = i < n; dots[i].visible = labels[i].visible = trails[i].visible = on;
      if (on) { dots[i].position.set(zr[i], zi[i], 0.3); labels[i].position.set(zr[i] + 0.2, zi[i] + 0.2, 0.4); }
    }
    cMark.position.set(c[0], c[1], 0.5); cLab.position.set(c[0] + 0.28, c[1] + 0.2, 0.5);
    const r = Math.hypot(c[0], c[1]); cir.scale.set(Math.max(r, 1e-3), Math.max(r, 1e-3), 1);
    cOut.set(c[0].toFixed(2) + (c[1] < 0 ? ' − ' : ' + ') + Math.abs(c[1]).toFixed(2) + 'i');
    rOut.set(residual(P.coef(c), n).toExponential(1));
    ctx.invalidate();
  }
  function cycles(perm) { // perm[i] = start index of the root now sitting where root i is
    const n = perm.length, seen = new Array(n).fill(false), out = [];
    for (let i = 0; i < n; i++) if (!seen[i]) { const cyc = []; let j = i; while (!seen[j]) { seen[j] = true; cyc.push(j + 1); j = perm[j]; } if (cyc.length > 1) out.push('(' + cyc.join(' ') + ')'); }
    return out.length ? out.join('') : 'identity';
  }

  function setKind(k) { kind = k; running = false; playBtn.el.textContent = 'Loop c once'; c = [...C0]; solveAt(C0[0], C0[1], false); clearTrails(); pOut.set('none yet'); refresh(); }
  ctx.ui.select({ label: 'Polynomial', options: Object.entries(polys).map(([k, v]) => [k, v.name]), value: kind, onChange: setKind });
  let running = false, ang = 0, r0 = 1, a0 = 0;
  const playBtn = ctx.ui.button({ label: 'Loop c once', onClick: () => {
    if (running) { running = false; playBtn.el.textContent = 'Loop c once'; return; }
    r0 = Math.max(Math.hypot(c[0], c[1]), 0.3); a0 = Math.atan2(c[1], c[0]); ang = 0; running = true; playBtn.el.textContent = 'Stop';
    for (let i = 0; i < MAXD; i++) { startR[i] = zr[i]; startI[i] = zi[i]; } clearTrails();
  } });
  ctx.ui.button({ label: 'Clear paths', onClick: clearTrails });
  ctx.loop((dt) => {
    if (!running) return;
    ang = Math.min(ang + dt * 0.8, Math.PI * 2);
    if (ang === 0) return; moveTo(r0 * Math.cos(a0 + ang), r0 * Math.sin(a0 + ang));
    if (ang >= Math.PI * 2) {
      running = false; playBtn.el.textContent = 'Loop c once'; const n = polys[kind].n, perm = [];
      for (let i = 0; i < n; i++) { let b = 0, bd = 1e9; for (let j = 0; j < n; j++) { const d = Math.hypot(zr[i] - startR[j], zi[i] - startI[j]); if (d < bd) { bd = d; b = j; } } perm.push(b); }
      pOut.set(perm.map((p, i) => (i + 1) + '→' + (p + 1)).join(' ') + '  cycle ' + cycles(perm));
    }
  });
  ctx.pointer(st.renderer.domElement, {
    down: (p) => drag(p), move: (p, d) => { if (d) drag(p); },
  });
  function drag(p) {
    running = false; playBtn.el.textContent = 'Loop c once';
    const { w, h } = ctx.size(); let x = p.x * st.height / 2 * w / h, y = p.y * st.height / 2; const r = Math.hypot(x, y);
    if (r > CMAX) { x *= CMAX / r; y *= CMAX / r; } moveTo(x, y);
  }

  ctx.onTheme((p) => {
    const cl = [p.c1, p.c2, p.c3, p.c4, p.c5];
    for (let i = 0; i < MAXD; i++) { dotMats[i].color.set(cl[i]); trailMats[i].color.set(cl[i]); }
    axMat.color.set(p.rule); cirMat.color.set(p.inkSoft); cMat.color.set(p.ink);
    labels.forEach((l) => l.userData.setColor(p.ink)); cLab.userData.setColor(p.ink);
  });
  solveAt(C0[0], C0[1], false); pushTrail(); pOut.set('none yet'); refresh();
}
