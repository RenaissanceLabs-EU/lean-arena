// Harmonic analysis: a closed curve as a sum of rotating circles. The curve is sampled (M points), its discrete
// Fourier transform c_k = (1/M) sum_n z_n e^{-2 pi i k n / M} is computed, and the N largest coefficients are kept.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, height: 3.8, pos: [0, 0, 10], controls: false });
  const M = 256, NMAX = 40, PERIOD = 14, SEG = 56, TR = 260, NA = 400;
  let shape = 'square', N = 3, tt = 0, playing = !ctx.reduced, coef = [], c0 = [0, 0], pal = ctx.palette();

  function resample(pts) { // closed polyline -> M points equally spaced in arc length
    const n = pts.length, cum = [0]; for (let i = 0; i < n; i++) { const a = pts[i], b = pts[(i + 1) % n]; cum.push(cum[i] + Math.hypot(b[0] - a[0], b[1] - a[1])); }
    const out = [], L = cum[n]; let j = 0;
    for (let m = 0; m < M; m++) { const s = L * m / M; while (cum[j + 1] < s) j++; const a = pts[j], b = pts[(j + 1) % n], u = (s - cum[j]) / (cum[j + 1] - cum[j]); out.push([a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u]); }
    return out;
  }
  const shapes = {
    square: { name: 'Square wave path', make: () => resample([[-1.8, -0.8], [-1.8, 0.6], [-1.2, 0.6], [-1.2, -0.2], [-0.6, -0.2], [-0.6, 0.6], [0, 0.6], [0, -0.2], [0.6, -0.2], [0.6, 0.6], [1.2, 0.6], [1.2, -0.2], [1.8, -0.2], [1.8, -0.8]]) },
    heart: { name: 'Heart', make: () => { const p = []; for (let i = 0; i < 2000; i++) { const t = i / 2000 * 2 * Math.PI; p.push([16 * Math.pow(Math.sin(t), 3) / 9, (13 * Math.cos(t) - 5 * Math.cos(2 * t) - 2 * Math.cos(3 * t) - Math.cos(4 * t)) / 9 + 0.5]); } return resample(p); } },
    star: { name: 'Star', make: () => { const p = []; for (let i = 0; i < 10; i++) { const r = i % 2 ? 0.75 : 1.8, a = Math.PI / 2 + i * Math.PI / 5; p.push([r * Math.cos(a), r * Math.sin(a) - 0.1]); } return resample(p); } },
  };
  let orig = [];
  function analyze() {
    orig = shapes[shape].make(); const all = [];
    for (let k = -M / 2; k < M / 2; k++) {
      let re = 0, im = 0;
      for (let n = 0; n < M; n++) { const ph = -2 * Math.PI * ((k * n) % M) / M, cs = Math.cos(ph), sn = Math.sin(ph); re += orig[n][0] * cs - orig[n][1] * sn; im += orig[n][0] * sn + orig[n][1] * cs; }
      re /= M; im /= M; if (k === 0) c0 = [re, im]; else all.push({ k, re, im, r: Math.hypot(re, im) });
    }
    all.sort((p, q) => q.r - p.r); coef = all.slice(0, NMAX);
  }
  function mk(max, color, loop) {
    const geo = new T.BufferGeometry(); const pos = new Float32Array(max * 3); geo.setAttribute('position', new T.BufferAttribute(pos, 3)); geo.setDrawRange(0, 0);
    const mat = new T.LineBasicMaterial({ color, transparent: true }); const o = loop ? new T.LineLoop(geo, mat) : new T.Line(geo, mat); o.frustumCulled = false; st.scene.add(o); return { o, mat, pos, geo };
  }
  const origL = mk(M, pal.rule, true), approx = mk(NA, pal.c2, true), trail = mk(TR, pal.c1, false);
  const chain = mk(NMAX + 1, pal.ink, false);
  const cg = new T.BufferGeometry(); const cpos = new Float32Array(NMAX * SEG * 6); cg.setAttribute('position', new T.BufferAttribute(cpos, 3)); cg.setDrawRange(0, 0);
  const cmat = new T.LineBasicMaterial({ transparent: true, opacity: 0.55 }); const circles = new T.LineSegments(cg, cmat); circles.frustumCulled = false; st.scene.add(circles);
  const tip = new T.Mesh(new T.CircleGeometry(0.06, 20), new T.MeshBasicMaterial()); tip.position.z = 1; st.scene.add(tip);
  const rmsOut = ctx.ui.readout({ label: 'Typical distance from the curve (RMS)' }), freqOut = ctx.ui.readout({ label: 'Highest frequency used' });
  let nt = 0;
  function evalAt(t, n, out) { let x = c0[0], y = c0[1]; for (let j = 0; j < n; j++) { const c = coef[j], ph = 2 * Math.PI * c.k * t, cs = Math.cos(ph), sn = Math.sin(ph); x += c.re * cs - c.im * sn; y += c.re * sn + c.im * cs; } out[0] = x; out[1] = y; }
  const tmp = [0, 0];
  function setN() {
    origL.geo.setDrawRange(0, M); for (let i = 0; i < M; i++) { origL.pos[i * 3] = orig[i][0]; origL.pos[i * 3 + 1] = orig[i][1]; } origL.geo.attributes.position.needsUpdate = true;
    for (let i = 0; i < NA; i++) { evalAt(i / NA, N, tmp); approx.pos[i * 3] = tmp[0]; approx.pos[i * 3 + 1] = tmp[1]; } approx.geo.setDrawRange(0, NA); approx.geo.attributes.position.needsUpdate = true;
    let e = 0; for (let i = 0; i < M; i++) { evalAt(i / M, N, tmp); e += (tmp[0] - orig[i][0]) ** 2 + (tmp[1] - orig[i][1]) ** 2; }
    rmsOut.set(Math.sqrt(e / M).toFixed(3)); let fm = 0; for (let j = 0; j < N; j++) fm = Math.max(fm, Math.abs(coef[j].k)); freqOut.set(String(fm));
    nt = 0; trail.geo.setDrawRange(0, 0); frame(0);
  }
  function frame(dt) {
    if (playing) tt = (tt + dt / PERIOD) % 1;
    let x = c0[0], y = c0[1]; chain.pos[0] = x; chain.pos[1] = y; chain.pos[2] = 0; let ns = 0;
    for (let j = 0; j < N; j++) {
      const c = coef[j], ph = 2 * Math.PI * c.k * tt, cs = Math.cos(ph), sn = Math.sin(ph), dx = c.re * cs - c.im * sn, dy = c.re * sn + c.im * cs;
      for (let s = 0; s < SEG; s++) { const a = 2 * Math.PI * s / SEG, b = 2 * Math.PI * (s + 1) / SEG, o = ns * 6;
        cpos[o] = x + c.r * Math.cos(a); cpos[o + 1] = y + c.r * Math.sin(a); cpos[o + 2] = 0; cpos[o + 3] = x + c.r * Math.cos(b); cpos[o + 4] = y + c.r * Math.sin(b); cpos[o + 5] = 0; ns++; }
      x += dx; y += dy; chain.pos[(j + 1) * 3] = x; chain.pos[(j + 1) * 3 + 1] = y; chain.pos[(j + 1) * 3 + 2] = 0;
    }
    cg.setDrawRange(0, ns * 2); cg.attributes.position.needsUpdate = true; chain.geo.setDrawRange(0, N + 1); chain.geo.attributes.position.needsUpdate = true;
    tip.position.set(x, y, 1);
    if (playing && dt > 0) { if (nt === TR) { trail.pos.copyWithin(0, 3); nt--; } trail.pos[nt * 3] = x; trail.pos[nt * 3 + 1] = y; nt++; trail.geo.setDrawRange(0, nt); trail.geo.attributes.position.needsUpdate = true; }
    ctx.invalidate();
  }
  ctx.ui.select({ label: 'Curve', options: Object.entries(shapes).map(([k, v]) => [k, v.name]), value: shape, onChange: (k) => { shape = k; analyze(); setN(); } });
  ctx.ui.slider({ label: 'Number of circles N', min: 1, max: NMAX, step: 1, value: N, onInput: (v) => { N = v; setN(); } });
  const pb = ctx.ui.button({ label: playing ? 'Pause' : 'Play', onClick: () => { playing = !playing; pb.el.textContent = playing ? 'Pause' : 'Play'; } });
  ctx.loop((dt) => { if (playing) frame(dt); });
  const fit = () => { const { w, h } = ctx.size(); st.camera.zoom = Math.min(1, (w / h * st.height) / 5.8); st.camera.updateProjectionMatrix(); ctx.invalidate(); };
  const ro = new ResizeObserver(fit); ro.observe(root); fit();
  ctx.onTheme((p) => { pal = p; origL.mat.color.set(p.inkSoft); origL.mat.opacity = 0.45; approx.mat.color.set(p.c2); trail.mat.color.set(p.c1); chain.mat.color.set(p.ink); cmat.color.set(p.inkSoft); tip.material.color.set(p.c3); });
  tt = 0.02; analyze(); setN();
  return { dispose() { ro.disconnect(); } };
}
