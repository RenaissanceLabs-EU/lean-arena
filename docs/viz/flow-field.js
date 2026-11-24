// ODEs: dx/dt = A x. The trace tau and determinant delta of A decide the picture. A is built from the
// eigenvalues (roots of l^2 - tau l + delta), and the origin is classified from exact integer arithmetic.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, height: 5, pos: [0, 0, 10], controls: false });
  const WX = 4.2, WY = 2.5, NPART = 360, H = 16, DT = 0.01;
  let ti = 0, di = 20; // tau = ti / 10, delta = di / 10 (integers: boundaries decided exactly)
  let a = 0, b = 0, c = 0, d = 0, playing = !ctx.reduced, pal = ctx.palette();
  const presets = { saddle: ['Saddle', 0, -20], snode: ['Stable node', -30, 20], unode: ['Unstable node', 30, 20], sspiral: ['Stable spiral', -10, 20], uspiral: ['Unstable spiral', 10, 20], center: ['Center', 0, 20], degen: ['Degenerate node', -20, 10] };

  function classify(t, dl) { // t = 10 tau, dl = 10 delta; tau^2 - 4 delta = (t^2 - 40 dl) / 100
    const disc = t * t - 40 * dl;
    if (dl < 0) return 'Saddle (unstable)';
    if (dl === 0) return 'Degenerate (a zero eigenvalue: a whole line of equilibria)';
    if (disc > 0) return t < 0 ? 'Stable node' : t > 0 ? 'Unstable node' : 'Saddle';
    if (disc === 0) return t < 0 ? 'Degenerate stable node (repeated eigenvalue)' : t > 0 ? 'Degenerate unstable node (repeated eigenvalue)' : 'Degenerate';
    return t < 0 ? 'Stable spiral' : t > 0 ? 'Unstable spiral' : 'Center';
  }
  function setMatrix() {
    const tau = ti / 10, del = di / 10, disc = ti * ti - 40 * di;
    if (disc > 0) { const s = Math.sqrt(disc) / 10; a = (tau + s) / 2; d = (tau - s) / 2; b = 0; c = 0; }
    else if (disc < 0) { const w = Math.sqrt(-disc) / 10 / 2; a = d = tau / 2; b = -w; c = w; }
    else { a = d = tau / 2; b = 1; c = 0; }
    return { tau, del, disc };
  }
  const clsOut = ctx.ui.readout({ label: 'Origin' }), eigOut = ctx.ui.readout({ label: 'Eigenvalues' }), discOut = ctx.ui.readout({ label: 'τ² − 4Δ' });
  function update() {
    const { tau, del, disc } = setMatrix(); clsOut.set(classify(ti, di));
    discOut.set((disc / 100).toFixed(2) + (disc > 0 ? '  (> 0)' : disc < 0 ? '  (< 0)' : '  (= 0)'));
    const f = (v) => (Math.abs(v) < 5e-10 ? 0 : v).toFixed(2);
    if (disc >= 0) { const s = Math.sqrt(disc) / 10; eigOut.set(f((tau + s) / 2) + ',  ' + f((tau - s) / 2)); }
    else { const w = Math.sqrt(-disc) / 20; eigOut.set(f(tau / 2) + ' ± ' + w.toFixed(2) + ' i'); }
    ctx.invalidate();
  }

  // particles with trails; positions integrated with RK4 at a fixed step (stable while |lambda| DT < 2.7)
  const px = new Float32Array(NPART), py = new Float32Array(NPART), age = new Float32Array(NPART), life = new Float32Array(NPART);
  const hist = new Float32Array(NPART * H * 2);
  const pos = new Float32Array(NPART * (H - 1) * 6), col = new Float32Array(NPART * (H - 1) * 8);
  const geo = new T.BufferGeometry(); geo.setAttribute('position', new T.BufferAttribute(pos, 3)); geo.setAttribute('color', new T.BufferAttribute(col, 4));
  const mat = new T.LineBasicMaterial({ vertexColors: true, transparent: true }); const trails = new T.LineSegments(geo, mat); trails.frustumCulled = false; st.scene.add(trails);
  const hg = new T.BufferGeometry(); const hpos = new Float32Array(NPART * 3); hg.setAttribute('position', new T.BufferAttribute(hpos, 3));
  const heads = new T.Points(hg, new T.PointsMaterial({ size: 3, sizeAttenuation: false })); heads.frustumCulled = false; st.scene.add(heads);
  function rk4(i) {
    const x = px[i], y = py[i];
    const k1x = a * x + b * y, k1y = c * x + d * y, x2 = x + DT / 2 * k1x, y2 = y + DT / 2 * k1y;
    const k2x = a * x2 + b * y2, k2y = c * x2 + d * y2, x3 = x + DT / 2 * k2x, y3 = y + DT / 2 * k2y;
    const k3x = a * x3 + b * y3, k3y = c * x3 + d * y3, x4 = x + DT * k3x, y4 = y + DT * k3y;
    const k4x = a * x4 + b * y4, k4y = c * x4 + d * y4;
    px[i] = x + DT / 6 * (k1x + 2 * k2x + 2 * k3x + k4x); py[i] = y + DT / 6 * (k1y + 2 * k2y + 2 * k3y + k4y);
  }
  const STEPS = 3; // RK4 steps between trail samples (0.03 time units)
  function spawn(i, initial) {
    px[i] = (Math.random() * 2 - 1) * (WX - 0.4); py[i] = (Math.random() * 2 - 1) * (WY - 0.3); age[i] = 0; life[i] = 2.5 + Math.random() * 3.5; if (initial) age[i] = Math.random() * life[i];
    const o = i * H * 2; for (let k = 0; k < H; k++) { hist[o + k * 2] = px[i]; hist[o + k * 2 + 1] = py[i]; }
    for (let k = 0; k < H; k++) { for (let s = 0; s < STEPS; s++) rk4(i); hist[o + k * 2] = px[i]; hist[o + k * 2 + 1] = py[i]; } // pre-run so the trail exists at once
  }
  function fill() {
    for (let i = 0; i < NPART; i++) {
      const o = i * H * 2; hpos[i * 3] = hist[o + (H - 1) * 2]; hpos[i * 3 + 1] = hist[o + (H - 1) * 2 + 1];
      for (let k = 0; k < H - 1; k++) {
        const s = (i * (H - 1) + k) * 6, cc = (i * (H - 1) + k) * 8, al0 = k / (H - 1), al1 = (k + 1) / (H - 1);
        pos[s] = hist[o + k * 2]; pos[s + 1] = hist[o + k * 2 + 1]; pos[s + 3] = hist[o + k * 2 + 2]; pos[s + 4] = hist[o + k * 2 + 3];
        col[cc] = col[cc + 4] = pal.c2r; col[cc + 1] = col[cc + 5] = pal.c2g; col[cc + 2] = col[cc + 6] = pal.c2b; col[cc + 3] = al0 * al0 * 0.9; col[cc + 7] = al1 * al1 * 0.9;
      }
    }
    geo.attributes.position.needsUpdate = true; geo.attributes.color.needsUpdate = true; hg.attributes.position.needsUpdate = true;
  }
  function step(dt) {
    for (let i = 0; i < NPART; i++) {
      for (let s = 0; s < STEPS; s++) rk4(i);
      age[i] += STEPS * DT; const o = i * H * 2; hist.copyWithin(o, o + 2, o + H * 2); hist[o + (H - 1) * 2] = px[i]; hist[o + (H - 1) * 2 + 1] = py[i];
      if (age[i] > life[i] || Math.abs(px[i]) > WX || Math.abs(py[i]) > WY || px[i] * px[i] + py[i] * py[i] < 0.04 || !isFinite(px[i] + py[i])) spawn(i);
    }
  }
  // axes and the line of the real eigen-directions (drawn only when they exist)
  const ax = new T.LineSegments(new T.BufferGeometry().setFromPoints([new T.Vector3(-WX, 0, 0), new T.Vector3(WX, 0, 0), new T.Vector3(0, -WY, 0), new T.Vector3(0, WY, 0)]), new T.LineBasicMaterial({ transparent: true, opacity: 0.6 }));
  const fr = new T.LineSegments(new T.EdgesGeometry(new T.PlaneGeometry(2 * WX, 2 * WY)), new T.LineBasicMaterial()); st.scene.add(ax, fr);
  const orig = new T.Mesh(new T.CircleGeometry(0.07, 20), new T.MeshBasicMaterial()); orig.position.z = 1; st.scene.add(orig);

  const sel = ctx.ui.select({ label: 'Preset', options: Object.entries(presets).map(([k, v]) => [k, v[0]]), value: 'sspiral', onChange: (k) => { const p = presets[k]; tS.set(p[1]); dS.set(p[2]); } });
  const tS = ctx.ui.slider({ label: 'Trace τ', min: -40, max: 40, step: 1, value: ti, format: (v) => (v / 10).toFixed(1), onInput: (v) => { ti = v; update(); } });
  const dS = ctx.ui.slider({ label: 'Determinant Δ', min: -40, max: 50, step: 1, value: di, format: (v) => (v / 10).toFixed(1), onInput: (v) => { di = v; update(); } });
  const pb = ctx.ui.button({ label: playing ? 'Pause' : 'Play', onClick: () => { playing = !playing; pb.el.textContent = playing ? 'Pause' : 'Play'; } });
  for (let i = 0; i < NPART; i++) spawn(i, true);
  ctx.loop((dt) => { if (playing) { step(dt); } fill(); });
  const fit = () => { const { w, h } = ctx.size(); st.camera.zoom = Math.min(1, (w / h * st.height) / (2 * WX + 0.4)); st.camera.updateProjectionMatrix(); ctx.invalidate(); };
  const ro = new ResizeObserver(fit); ro.observe(root); fit();
  ctx.onTheme((p) => { pal = Object.assign({}, p); const c = new T.Color(p.c2); pal.c2r = c.r; pal.c2g = c.g; pal.c2b = c.b; heads.material.color.set(p.c1); ax.material.color.set(p.inkSoft); fr.material.color.set(p.rule); orig.material.color.set(p.ink); });
  tS.set(-10); dS.set(20);
  return { dispose() { ro.disconnect(); } };
}
