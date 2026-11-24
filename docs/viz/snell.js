// Optics: light from A in air to B in glass takes the crossing point that minimizes travel time. That point obeys Snell's law.
export default function mount(root, ctx) {
  const T = ctx.THREE, CY = -0.95;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 8.6, pos: [0, CY, 10], target: [0, CY, 0] });
  const AX = -2.6, AY = 1.9, BX = 2.2, BY = -1.7, XMAX = 4.2, Y0 = -4.6, Y1 = -3.3, GLASS = -2.5;
  let n = 1.5, x = 0;
  const basic = (o) => new T.MeshBasicMaterial(Object.assign({ side: T.DoubleSide }, o));
  const tm = (px) => Math.hypot(px - AX, AY) + n * Math.hypot(BX - px, BY); // time, with c = 1 in air
  function argmin() { let lo = -XMAX, hi = XMAX; for (let i = 0; i < 100; i++) { const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3; if (tm(m1) < tm(m2)) hi = m2; else lo = m1; } return (lo + hi) / 2; }

  function ribbon(mat, maxN, z) {
    const g = new T.BufferGeometry(), pos = new Float32Array(maxN * 6), idx = [];
    for (let i = 0; i < maxN - 1; i++) { const a = 2 * i; idx.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
    g.setAttribute('position', new T.BufferAttribute(pos, 3)); g.setIndex(idx);
    const m = new T.Mesh(g, mat); m.frustumCulled = false; st.scene.add(m);
    m.userData.set = (pts, w) => {
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
  const glass = new T.Mesh(new T.PlaneGeometry(30, -GLASS), basic({ transparent: true, depthWrite: false })); glass.position.set(0, GLASS / 2, -1); st.scene.add(glass);
  const mats = { surf: basic({}), ax: basic({}), curve: basic({}), air: basic({}), gl: basic({}), norm: basic({ transparent: true, opacity: 0.6 }), drop: basic({ transparent: true, opacity: 0.55 }), arc1: basic({}), arc2: basic({}) };
  const surf = ribbon(mats.surf, 2, 0), ax = ribbon(mats.ax, 2, 0), curve = ribbon(mats.curve, 150, 0.1);
  const rAir = ribbon(mats.air, 2, 0.3), rGl = ribbon(mats.gl, 2, 0.3), norm = ribbon(mats.norm, 2, 0.05), drop = ribbon(mats.drop, 2, 0.05);
  const arc1 = ribbon(mats.arc1, 24, 0.35), arc2 = ribbon(mats.arc2, 24, 0.35);
  surf.userData.set([[-9, 0], [9, 0]], 0.03); ax.userData.set([[-XMAX, Y0], [XMAX, Y0]], 0.02);

  const circ = new T.CircleGeometry(1, 24);
  const mk = (r, z) => { const m = new T.Mesh(circ, basic({})); m.scale.set(r, r, 1); m.position.z = z; st.scene.add(m); return m; };
  const ptA = mk(0.17, 0.5), ptB = mk(0.17, 0.5), handleO = mk(0.24, 0.6), handleI = mk(0.15, 0.61), dot = mk(0.12, 0.4), best = mk(0.2, 0.39), bestI = mk(0.14, 0.395);
  ptA.position.set(AX, AY, 0.5); ptB.position.set(BX, BY, 0.5);
  const lab = (t, px, py, o) => { const l = ctx.label(t, Object.assign({ size: 0.34 }, o)); l.position.set(px, py, 1); st.scene.add(l); return l; };
  const lA = lab('A', AX - 0.35, AY + 0.1, { bold: true }), lB = lab('B', BX + 0.35, BY - 0.1, { bold: true });
  const lAir = lab('air, n = 1', -3.3, 2.7, { size: 0.3 }), lGl = lab('glass', -3.2, -2.1, { size: 0.3 }), lT = lab('travel time for each crossing point', 0, Y1 + 0.55, { size: 0.3 });
  const lt1 = lab('θ1', 0, 0, { size: 0.3, bold: true }), lt2 = lab('θ2', 0, 0, { size: 0.3, bold: true }), lMin = lab('fastest', 0, 0, { size: 0.26 });

  const outA1 = ctx.ui.readout({ label: 'Angle θ1 in air / θ2 in glass' }), outR = ctx.ui.readout({ label: 'sin θ1 / sin θ2' }), outN = ctx.ui.readout({ label: 'n2 / n1' });
  const outT = ctx.ui.readout({ label: 'Travel time (c = 1) / fastest' });

  function update() {
    const xs = argmin(), tmin = tm(xs); let tmax = 0; for (let i = 0; i <= 140; i++) tmax = Math.max(tmax, tm(-XMAX + 2 * XMAX * i / 140));
    const Y = (t) => Y0 + (t - tmin) / Math.max(1e-9, tmax - tmin) * (Y1 - Y0);
    const pts = []; for (let i = 0; i <= 140; i++) { const px = -XMAX + 2 * XMAX * i / 140; pts.push([px, Y(tm(px))]); }
    curve.userData.set(pts, 0.035);
    const d1 = Math.hypot(x - AX, AY), d2 = Math.hypot(BX - x, BY), s1 = (x - AX) / d1, s2 = (BX - x) / d2;
    rAir.userData.set([[AX, AY], [x, 0]], 0.05); rGl.userData.set([[x, 0], [BX, BY]], 0.05);
    norm.userData.set([[x, 1.5], [x, GLASS + 0.2]], 0.015); drop.userData.set([[x, GLASS], [x, Y(tm(x))]], 0.015);
    // angle arcs measured from the normal at the crossing point
    const arc = (a0, a1, g) => { const q = []; for (let i = 0; i <= 20; i++) { const a = a0 + (a1 - a0) * i / 20; q.push([x + 0.75 * Math.cos(a), 0.75 * Math.sin(a)]); } g.userData.set(q, 0.03); return (a0 + a1) / 2; };
    const m1 = arc(Math.PI / 2, Math.atan2(AY, AX - x), arc1), m2 = arc(-Math.PI / 2, Math.atan2(BY, BX - x), arc2);
    lt1.position.set(x + 1.15 * Math.cos(m1), 1.15 * Math.sin(m1), 1); lt2.position.set(x + 1.15 * Math.cos(m2), 1.15 * Math.sin(m2), 1);
    handleO.position.set(x, 0, 0.6); handleI.position.set(x, 0, 0.61); dot.position.set(x, Y(tm(x)), 0.4);
    best.position.set(xs, Y(tmin), 0.39); bestI.position.set(xs, Y(tmin), 0.395); lMin.position.set(xs, Y(tmin) - 0.38, 1);
    outA1.set((Math.asin(Math.abs(s1)) * 180 / Math.PI).toFixed(1) + '°  /  ' + (Math.asin(Math.abs(s2)) * 180 / Math.PI).toFixed(1) + '°');
    outR.set(Math.abs(s2) < 1e-6 ? '—' : (s1 / s2).toFixed(3)); outN.set(n.toFixed(3));
    outT.set(tm(x).toFixed(3) + '  /  ' + tmin.toFixed(3));
    glass.material.opacity = 0.08 + 0.3 * (n - 1) / 1; lGl.userData.setText('glass, n = ' + n.toFixed(2));
    ctx.invalidate();
  }

  const slX = ctx.ui.slider({ label: 'Crossing point', min: -XMAX, max: XMAX, step: 0.01, value: x, onInput: (v) => { x = v; update(); } });
  ctx.ui.slider({ label: 'Glass index n2', min: 1, max: 2, step: 0.01, value: n, onInput: (v) => { n = v; update(); } });
  ctx.ui.button({ label: 'Snap to fastest', onClick: () => { slX.set(argmin()); } });
  ctx.pointer(st.renderer.domElement, {
    down: (p) => slX.set(Math.max(-XMAX, Math.min(XMAX, p.x * st.camera.right))),
    move: (p, down) => { if (down) slX.set(Math.max(-XMAX, Math.min(XMAX, p.x * st.camera.right))); },
  });

  ctx.onTheme((p) => {
    mats.surf.color.set(p.ink); mats.ax.color.set(p.rule); mats.curve.color.set(p.ink); mats.air.color.set(p.c1); mats.gl.color.set(p.c3);
    mats.norm.color.set(p.inkSoft); mats.drop.color.set(p.inkSoft); mats.arc1.color.set(p.c1); mats.arc2.color.set(p.c3);
    glass.material.color.set(p.c2); ptA.material.color.set(p.c1); ptB.material.color.set(p.c3);
    handleO.material.color.set(p.ink); handleI.material.color.set(p.paper); dot.material.color.set(p.ink); best.material.color.set(p.c5); bestI.material.color.set(p.paper);
    [lA, lB, lAir, lGl, lT, lt1, lt2, lMin].forEach(l => l.userData.setColor(p.inkSoft)); lt1.userData.setColor(p.c1); lt2.userData.setColor(p.c3); lA.userData.setColor(p.c1); lB.userData.setColor(p.c3);
  });
  x = argmin(); slX.set(x);
}
