// Probability: a Galton board. Each peg is a fair coin flip; the bins collect a binomial histogram that approaches a bell curve.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 10.4, pos: [0, 0, 10] });
  const TOP = 4.4, BOT = 0.6, FLOOR = -4.25, HMAX = 3.6, MAXB = 160, SEG = 0.2, FALL = 0.35, MAXN = 14;
  let n = 10, dx = 0.6, dy = 0.4, ballR = 0.12, u = 0.1, total = 0, pmf = [], pmax = 0;
  const counts = new Array(MAXN + 1).fill(0);
  const dummy = new T.Object3D();
  const inst = (geo, mat, cnt) => { const m = new T.InstancedMesh(geo, mat, cnt); m.frustumCulled = false; st.scene.add(m); return m; };
  const setM = (mesh, i, x, y, z, sx, sy) => { dummy.position.set(x, y, z); dummy.scale.set(sx, sy, 1); dummy.updateMatrix(); mesh.setMatrixAt(i, dummy.matrix); };
  const basic = (o) => new T.MeshBasicMaterial(Object.assign({ side: T.DoubleSide }, o));

  function ribbon(mat, maxN) { // a thick polyline as a triangle strip
    const g = new T.BufferGeometry(), pos = new Float32Array(maxN * 6), idx = [];
    for (let i = 0; i < maxN - 1; i++) { const a = 2 * i; idx.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
    g.setAttribute('position', new T.BufferAttribute(pos, 3)); g.setIndex(idx);
    const m = new T.Mesh(g, mat); m.frustumCulled = false; st.scene.add(m);
    m.userData.set = (pts, w, z) => {
      const k = pts.length;
      for (let i = 0; i < k; i++) {
        const a = pts[Math.max(0, i - 1)], b = pts[Math.min(k - 1, i + 1)];
        let tx = b[0] - a[0], ty = b[1] - a[1]; const l = Math.hypot(tx, ty) || 1; tx /= l; ty /= l;
        pos.set([pts[i][0] - ty * w, pts[i][1] + tx * w, z, pts[i][0] + ty * w, pts[i][1] - tx * w, z], i * 6);
      }
      g.setDrawRange(0, (k - 1) * 6); g.attributes.position.needsUpdate = true;
    };
    return m;
  }

  const pegs = inst(new T.CircleGeometry(1, 16), basic({}), 105);
  const bars = inst(new T.PlaneGeometry(1, 1).translate(0, 0.5, 0), basic({ transparent: true, opacity: 0.75, depthWrite: false }), MAXN + 1);
  const rings = inst(new T.RingGeometry(0.62, 1, 20), basic({}), MAXN + 1);
  const balls = inst(new T.CircleGeometry(1, 16), basic({}), MAXB);
  const curveMat = basic({}), floorMat = basic({});
  const curve = ribbon(curveMat, 200), floorLine = ribbon(floorMat, 2);
  floorLine.userData.set([[-7, FLOOR], [7, FLOOR]], 0.025, 0);
  const labels = []; for (let k = 0; k <= MAXN; k++) { const l = ctx.label(String(k), { size: 0.34 }); l.position.z = 1; st.scene.add(l); labels.push(l); }
  const tag = ctx.label('number of right bounces', { size: 0.3 }); tag.position.set(0, FLOOR - 0.72, 1); st.scene.add(tag);
  const out = ctx.ui.readout({ label: 'Balls dropped' });

  // ball pool
  const active = new Uint8Array(MAXB), tt = new Float32Array(MAXB), dirs = new Uint8Array(MAXB * MAXN);
  let pending = 0, spawnT = 0;
  function spawn() {
    for (let b = 0; b < MAXB; b++) if (!active[b]) { active[b] = 1; tt[b] = 0; for (let j = 0; j < n; j++) dirs[b * MAXN + j] = Math.random() < 0.5 ? 1 : 0; return true; }
    return false;
  }
  const kAt = (b, j) => { let k = 0; for (let i = 0; i < j; i++) k += dirs[b * MAXN + i]; return k; };
  function node(b, s, out2) { // node 0 spawn, 1..n pegs of rows 0..n-1, n+1 landing
    if (s === 0) { out2[0] = 0; out2[1] = TOP + 0.6; }
    else if (s <= n) { const r = s - 1; out2[0] = (kAt(b, r) - r / 2) * dx; out2[1] = TOP - r * dy; }
    else { const k = kAt(b, n); out2[0] = (k - n / 2) * dx; out2[1] = FLOOR + counts[k] * u + ballR; }
  }
  const A = [0, 0], B = [0, 0];

  function layout() {
    dx = Math.min(1, 9.4 / (n + 1)); dy = (TOP - BOT) / (n - 1); ballR = Math.min(0.14, dx * 0.2);
    let row = [1]; for (let i = 0; i < n; i++) { const nr = [1]; for (let k = 1; k < row.length; k++) nr.push(row[k - 1] + row[k]); nr.push(1); row = nr; }
    pmf = row.map(c => c / Math.pow(2, n)); pmax = Math.max(...pmf);
    const pr = ballR * 0.55; let id = 0;
    for (let j = 0; j < n; j++) for (let i = 0; i <= j; i++) setM(pegs, id++, (i - j / 2) * dx, TOP - j * dy, 0, pr, pr);
    pegs.count = id; pegs.instanceMatrix.needsUpdate = true;
    for (let k = 0; k <= MAXN; k++) { const l = labels[k]; l.visible = k <= n; l.position.x = (k - n / 2) * dx; l.position.y = FLOOR - 0.3; }
    redraw();
  }
  function redraw() {
    let maxC = 0; for (let k = 0; k <= n; k++) maxC = Math.max(maxC, counts[k]);
    const ref = Math.max(total, 100); // the curves are drawn for at least 100 balls so the target is visible
    u = Math.min(0.45, HMAX / Math.max(maxC, ref * pmax));
    for (let k = 0; k <= n; k++) {
      const x = (k - n / 2) * dx;
      setM(bars, k, x, FLOOR, 0, dx * 0.86, counts[k] * u);
      setM(rings, k, x, FLOOR + ref * pmf[k] * u, 0.2, 0.09, 0.09);
    }
    bars.count = n + 1; rings.count = n + 1; bars.instanceMatrix.needsUpdate = true; rings.instanceMatrix.needsUpdate = true;
    const s = Math.sqrt(n) / 2, pts = [];
    for (let k = -0.7; k <= n + 0.7001; k += 0.1) pts.push([(k - n / 2) * dx, FLOOR + ref * Math.exp(-0.5 * ((k - n / 2) / s) ** 2) / (s * Math.sqrt(2 * Math.PI)) * u]);
    curve.userData.set(pts, 0.03, 0.1);
    out.set(String(total));
  }
  function clearAll() { counts.fill(0); total = 0; active.fill(0); pending = 0; for (let b = 0; b < MAXB; b++) setM(balls, b, 0, 0, 0, 0, 0); balls.instanceMatrix.needsUpdate = true; redraw(); }
  function preload(m) { for (let i = 0; i < m; i++) { let k = 0; for (let j = 0; j < n; j++) k += Math.random() < 0.5 ? 1 : 0; counts[k]++; total++; } redraw(); }

  ctx.ui.slider({ label: 'Rows of pegs', min: 4, max: MAXN, step: 1, value: n, onInput: (v) => { n = v; layout(); clearAll(); preload(400); } });
  ctx.ui.button({ label: 'Drop 1', onClick: () => { pending += 1; } });
  ctx.ui.button({ label: 'Drop 100', onClick: () => { pending += 100; } });
  ctx.ui.button({ label: 'Reset', onClick: () => { clearAll(); } });

  ctx.loop((dt) => {
    if (pending > 0) { spawnT -= dt; while (pending > 0 && spawnT <= 0) { if (!spawn()) break; pending--; spawnT += 0.045; } }
    else spawnT = 0;
    let dirty = false;
    for (let b = 0; b < MAXB; b++) {
      if (!active[b]) continue;
      tt[b] += dt; const t = tt[b];
      const s = Math.min(Math.floor(t / SEG), n), f = Math.min(1, s === n ? (t - n * SEG) / FALL : (t - s * SEG) / SEG);
      if (s === n && f >= 1) { const k = kAt(b, n); counts[k]++; total++; active[b] = 0; setM(balls, b, 0, 0, 0, 0, 0); dirty = true; continue; }
      node(b, s, A); node(b, s + 1, B);
      const sm = f * f * (3 - 2 * f);
      const x = A[0] + (B[0] - A[0]) * sm;
      let y = A[1] + (B[1] - A[1]) * f * f; if (s >= 1 && s < n) y += 0.16 * Math.sin(Math.PI * f) * (1 - f);
      setM(balls, b, x, y, 0.3, ballR, ballR);
    }
    balls.instanceMatrix.needsUpdate = true;
    if (dirty) redraw();
  });

  ctx.onTheme((p) => {
    pegs.material.color.set(p.inkSoft); bars.material.color.set(p.c2); rings.material.color.set(p.ink);
    balls.material.color.set(p.c1); curveMat.color.set(p.c3); floorMat.color.set(p.rule);
    labels.forEach(l => l.userData.setColor(p.inkSoft)); tag.userData.setColor(p.inkSoft);
  });
  layout(); clearAll(); preload(400);
}
