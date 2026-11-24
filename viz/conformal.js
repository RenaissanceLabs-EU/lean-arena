// Complex analysis: a square grid carried by w = (1 - t) z + t f(z). Where g'(z) is not zero, g keeps
// the right angle between a horizontal and a vertical grid line (it is conformal there).
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, height: 5.6, pos: [0, 0, 10], controls: false });
  const CX = 3.6, CY = 2.6, NP = 180;
  const range = (a, b, s) => { const r = []; for (let c = a; c <= b + 1e-9; c += s) r.push(Math.round(c / s) * s); return r; };
  const funcs = {
    sq: { name: 'z²', f: (x, y, o) => { o[0] = x * x - y * y; o[1] = 2 * x * y; }, d: (x, y, o) => { o[0] = 2 * x; o[1] = 2 * y; },
      hy: range(-1.5, 1.5, 0.25), hx: [-1.5, 1.5], vx: range(-1.5, 1.5, 0.25), vy: [-1.5, 1.5], crit: (s) => [[-s / 2, 0]] },
    ex: { name: 'eᶻ', f: (x, y, o) => { const e = Math.exp(x); o[0] = e * Math.cos(y); o[1] = e * Math.sin(y); }, d: (x, y, o) => { const e = Math.exp(x); o[0] = e * Math.cos(y); o[1] = e * Math.sin(y); },
      hy: range(-2.5, 2.5, 0.5), hx: [-2.5, 1], vx: range(-2.5, 1, 0.5), vy: [-2.5, 2.5], crit: () => [] },
    inv: { name: '1 / z', f: (x, y, o) => { const r = x * x + y * y; o[0] = x / r; o[1] = -y / r; }, d: (x, y, o) => { const r = x * x + y * y; o[0] = -(x * x - y * y) / (r * r); o[1] = 2 * x * y / (r * r); },
      hy: range(-1.5, 1.5, 0.25), hx: [-1.5, 1.5], vx: range(-1.5, 1.5, 0.25), vy: [-1.5, 1.5], crit: (s) => (s > 0 ? [[1 / Math.sqrt(s), 0], [-1 / Math.sqrt(s), 0]] : []) },
    sin: { name: 'sin z', f: (x, y, o) => { o[0] = Math.sin(x) * Math.cosh(y); o[1] = Math.cos(x) * Math.sinh(y); }, d: (x, y, o) => { o[0] = Math.cos(x) * Math.cosh(y); o[1] = -Math.sin(x) * Math.sinh(y); },
      hy: range(-1.5, 1.5, 0.25), hx: [-3, 3], vx: range(-3, 3, 0.5), vy: [-1.5, 1.5], crit: (s) => (s <= 1 ? [[Math.acos(-s), 0], [-Math.acos(-s), 0]] : []) },
    mob: { name: '(z − 1) / (z + 1)', f: (x, y, o) => { const r = (x + 1) * (x + 1) + y * y; o[0] = (x * x + y * y - 1) / r; o[1] = 2 * y / r; },
      d: (x, y, o) => { const a = x + 1, r = a * a + y * y; o[0] = 2 * (a * a - y * y) / (r * r); o[1] = -4 * a * y / (r * r); }, // 2/(z+1)^2
      hy: range(-3, 3, 0.5), hx: [-3, 3], vx: range(-3, 3, 0.5), vy: [-3, 3], crit: (s) => (s > 0 ? [[-1, Math.sqrt(2 / s)], [-1, -Math.sqrt(2 / s)]] : []) },
  };
  let key = 'sq', tv = 1, z0 = [0.5, 0.5], lines = [], pal = ctx.palette();
  const tmp = [0, 0];
  function g(x, y, t, o) { funcs[key].f(x, y, tmp); o[0] = (1 - t) * x + t * tmp[0]; o[1] = (1 - t) * y + t * tmp[1]; }

  function mk(maxSeg, color) {
    const geo = new T.BufferGeometry(); const pos = new Float32Array(maxSeg * 6);
    geo.setAttribute('position', new T.BufferAttribute(pos, 3)); geo.setDrawRange(0, 0);
    const mat = new T.LineBasicMaterial({ color, transparent: true }); const o = new T.LineSegments(geo, mat); o.frustumCulled = false; st.scene.add(o);
    return { o, mat, pos, geo, n: 0 };
  }
  const seg = (L, a, b, c, d) => { const k = L.n * 6; L.pos[k] = a; L.pos[k + 1] = b; L.pos[k + 2] = 0; L.pos[k + 3] = c; L.pos[k + 4] = d; L.pos[k + 5] = 0; L.n++; };
  const flush = (L) => { L.geo.setDrawRange(0, L.n * 2); L.geo.attributes.position.needsUpdate = true; };
  const MAXS = 30 * NP * 2;
  const srcL = mk(MAXS, pal.rule), hL = mk(MAXS, pal.c2), vL = mk(MAXS, pal.c3), frame = mk(8, pal.rule), mk1 = mk(64, pal.c2), mk2 = mk(64, pal.c3), mk3 = mk(64, pal.ink);
  hL.mat.opacity = vL.mat.opacity = 1; srcL.mat.opacity = 0.55;
  seg(frame, -CX, -CY, CX, -CY); seg(frame, CX, -CY, CX, CY); seg(frame, CX, CY, -CX, CY); seg(frame, -CX, CY, -CX, -CY); flush(frame);
  const circ = (r, col) => { const m = new T.Mesh(new T.CircleGeometry(r, 24), new T.MeshBasicMaterial({ color: col })); m.position.z = 1; st.scene.add(m); return m; };
  const dotSrc = circ(0.06, pal.inkSoft), dotImg = circ(0.075, pal.ink);
  const rings = [0, 1].map(() => { const m = new T.Mesh(new T.RingGeometry(0.11, 0.15, 28), new T.MeshBasicMaterial({ color: pal.c1 })); m.position.z = 1; st.scene.add(m); return m; });

  function build() {
    const F = funcs[key]; lines = [];
    F.hy.forEach((c) => lines.push({ h: true, a: F.hx[0], b: F.hx[1], c }));
    F.vx.forEach((c) => lines.push({ h: false, a: F.vy[0], b: F.vy[1], c }));
    srcL.n = 0;
    lines.forEach((l) => { for (let i = 0; i < NP; i++) { const u = l.a + (l.b - l.a) * i / NP, u2 = l.a + (l.b - l.a) * (i + 1) / NP; if (l.h) seg(srcL, u, l.c, u2, l.c); else seg(srcL, l.c, u, l.c, u2); } });
    srcL.n = srcL.n; flush(srcL);
  }
  const ok = (p) => isFinite(p[0]) && isFinite(p[1]) && Math.abs(p[0]) <= CX && Math.abs(p[1]) <= CY;
  const pa = [0, 0], pb = [0, 0], dd = [0, 0];
  const angleOut = ctx.ui.readout({ label: 'Angle between the two grid lines at the dot' }), scaleOut = ctx.ui.readout({ label: 'Local stretch factor |g′(z)|' });

  function update() {
    const F = funcs[key]; hL.n = 0; vL.n = 0;
    lines.forEach((l) => {
      const L = l.h ? hL : vL; let prevOk = false;
      for (let i = 0; i <= NP; i++) {
        const u = l.a + (l.b - l.a) * i / NP, x = l.h ? u : l.c, y = l.h ? l.c : u;
        let cur = (Math.hypot(x, y) < 1e-9 && key === 'inv') || (key === 'mob' && Math.hypot(x + 1, y) < 1e-9) ? null : (g(x, y, tv, pb), ok(pb) ? pb : null);
        if (cur && prevOk) seg(L, pa[0], pa[1], pb[0], pb[1]);
        prevOk = !!cur; pa[0] = pb[0]; pa[1] = pb[1];
      }
    });
    flush(hL); flush(vL);
    // marker: where the dot goes and what the two grid directions become
    const h = 1e-5; g(z0[0], z0[1], tv, pa); const gx = pa[0], gy = pa[1];
    g(z0[0] + h, z0[1], tv, pb); const ux = pb[0] - gx, uy = pb[1] - gy; g(z0[0], z0[1] + h, tv, pb); const vx = pb[0] - gx, vy = pb[1] - gy;
    const lu = Math.hypot(ux, uy), lv = Math.hypot(vx, vy);
    mk1.n = mk2.n = mk3.n = 0;
    dotSrc.position.set(z0[0], z0[1], 1); dotSrc.visible = Math.abs(z0[0]) < CX && Math.abs(z0[1]) < CY;
    const vis = isFinite(gx) && isFinite(gy) && Math.abs(gx) < CX && Math.abs(gy) < CY && lu > 0 && lv > 0 && isFinite(lu + lv);
    dotImg.visible = vis;
    if (isFinite(lu + lv) && lu > 0 && lv > 0) {
      const c = (ux * vx + uy * vy) / (lu * lv), ang = Math.acos(Math.max(-1, Math.min(1, c))) * 180 / Math.PI;
      angleOut.set(ang.toFixed(2) + '°'); F.d(z0[0], z0[1], dd); const gm = Math.hypot(dd[0] * tv + (1 - tv), dd[1] * tv);
      scaleOut.set(gm < 1e-3 ? 'about 0: critical point, angles are not preserved' : gm.toFixed(3));
      if (vis) {
        dotImg.position.set(gx, gy, 1);
        const e1x = ux / lu, e1y = uy / lu, e2x = vx / lv, e2y = vy / lv, L1 = 0.5, a = 0.14;
        for (const [dx, dy] of [[0, 0], [0.012, 0], [0, 0.012], [0.012, 0.012]]) {
          seg(mk1, gx + dx, gy + dy, gx + e1x * L1 + dx, gy + e1y * L1 + dy); seg(mk2, gx + dx, gy + dy, gx + e2x * L1 + dx, gy + e2y * L1 + dy);
        }
        seg(mk3, gx + e1x * a, gy + e1y * a, gx + (e1x + e2x) * a, gy + (e1y + e2y) * a); seg(mk3, gx + e2x * a, gy + e2y * a, gx + (e1x + e2x) * a, gy + (e1y + e2y) * a);
      }
    } else { angleOut.set('undefined here (the map blows up)'); scaleOut.set('—'); }
    flush(mk1); flush(mk2); flush(mk3);
    const cr = tv > 0 ? F.crit(tv >= 1 ? 0 : (1 - tv) / tv) : []; // critical points of g: f'(z) = -(1 - t) / t
    rings.forEach((r, i) => { const z = cr[i]; if (z && isFinite(z[0] + z[1])) { g(z[0], z[1], tv, pb); r.visible = isFinite(pb[0]) && Math.abs(pb[0]) < CX && Math.abs(pb[1]) < CY; r.position.set(pb[0], pb[1], 1); } else r.visible = false; });
    ctx.invalidate();
  }
  ctx.ui.select({ label: 'Function f(z)', options: Object.entries(funcs).map(([k, v]) => [k, v.name]), value: key, onChange: (k) => { key = k; build(); update(); } });
  ctx.ui.slider({ label: 'Morph t (0 = identity, 1 = f)', min: 0, max: 1, step: 0.01, value: tv, onInput: (v) => { tv = v; update(); } });
  const cam = st.camera;
  ctx.pointer(st.renderer.domElement, { move: (p, down) => { if (!down) return; z0 = [Math.max(-CX, Math.min(CX, p.x * cam.right / cam.zoom)), Math.max(-CY, Math.min(CY, p.y * cam.top / cam.zoom))]; update(); },
    down: (p) => { z0 = [Math.max(-CX, Math.min(CX, p.x * cam.right / cam.zoom)), Math.max(-CY, Math.min(CY, p.y * cam.top / cam.zoom))]; update(); } });
  const fit = () => { const { w, h } = ctx.size(); cam.zoom = Math.min(1, (w / h * st.height) / 7.6); cam.updateProjectionMatrix(); ctx.invalidate(); };
  const ro = new ResizeObserver(fit); ro.observe(root); fit();
  ctx.onTheme((p) => { pal = p; srcL.mat.color.set(p.inkSoft); srcL.mat.opacity = p.dark ? 0.35 : 0.4; hL.mat.color.set(p.c2); vL.mat.color.set(p.c3); frame.mat.color.set(p.rule); mk1.mat.color.set(p.c2); mk2.mat.color.set(p.c3); mk3.mat.color.set(p.ink);
    dotSrc.material.color.set(p.inkSoft); dotImg.material.color.set(p.ink); rings.forEach((r) => r.material.color.set(p.c1)); });
  build(); update();
  return { dispose() { ro.disconnect(); } };
}
