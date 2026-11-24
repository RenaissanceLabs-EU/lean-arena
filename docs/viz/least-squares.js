// Statistics: the least-squares line minimizes the total area of the squares built on the vertical residuals.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 8, pos: [0, 0, 10] });
  const MAXP = 20;
  const START = [[-3.2, -1.0], [-2.3, -1.6], [-1.5, 0.1], [-0.7, 0.2], [0.2, 1.6], [1.0, 0.4], [1.9, 1.9], [3.0, 1.5]];
  let pts = START.map(p => p.slice());
  let fit = null; // { m, b } or null when all x are equal
  const mine = { m: 0.2, b: -0.8, on: false };
  let seed = 7; const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
  const basic = (o) => new T.MeshBasicMaterial(Object.assign({ side: T.DoubleSide }, o));
  const half = () => ({ w: st.camera.right, h: st.camera.top });

  // axes
  const axMat = basic({}); const axes = [];
  for (let i = 0; i < 2; i++) { const m = new T.Mesh(new T.PlaneGeometry(1, 1), axMat); m.scale.set(i ? 0.02 : 40, i ? 40 : 0.02, 1); m.position.z = -0.1; st.scene.add(m); axes.push(m); }
  // thick straight lines
  const mkLine = (mat) => { const m = new T.Mesh(new T.PlaneGeometry(1, 1), mat); st.scene.add(m); return m; };
  const setLine = (m, s, b, w) => { m.position.set(0, b, 0.2); m.rotation.z = Math.atan(s); m.scale.set(80, w, 1); };
  const fitMat = basic({}), mineMat = basic({});
  const fitLine = mkLine(fitMat), mineLine = mkLine(mineMat);

  // dynamic squares and residual segments, one set for each line
  function dyn(mat) {
    const fill = new T.BufferGeometry(); fill.setAttribute('position', new T.BufferAttribute(new Float32Array(MAXP * 18), 3));
    const edge = new T.BufferGeometry(); edge.setAttribute('position', new T.BufferAttribute(new Float32Array(MAXP * 24), 3));
    const seg = new T.BufferGeometry(); seg.setAttribute('position', new T.BufferAttribute(new Float32Array(MAXP * 6), 3));
    const f = new T.Mesh(fill, mat.fill), e = new T.LineSegments(edge, mat.line), s = new T.LineSegments(seg, mat.line);
    [f, e, s].forEach(o => { o.frustumCulled = false; st.scene.add(o); });
    return { fill, edge, seg, f, e, s };
  }
  const fillMatA = basic({ transparent: true, opacity: 0.25, depthWrite: false }), lineMatA = new T.LineBasicMaterial();
  const fillMatB = basic({ transparent: true, opacity: 0.22, depthWrite: false }), lineMatB = new T.LineBasicMaterial();
  const dA = dyn({ fill: fillMatA, line: lineMatA }), dB = dyn({ fill: fillMatB, line: lineMatB });
  let showSq = true;

  function fillDyn(d, line, dir) {
    const F = d.fill.attributes.position.array, E = d.edge.attributes.position.array, S = d.seg.attributes.position.array;
    let nn = 0;
    if (line) for (const [x, y] of pts) {
      const ly = line.m * x + line.b, r = Math.abs(y - ly), x2 = x + dir * r, y0 = Math.min(y, ly), y1 = Math.max(y, ly);
      S.set([x, y, 0.15, x, ly, 0.15], nn * 6);
      F.set([x, y0, 0, x2, y0, 0, x2, y1, 0, x, y0, 0, x2, y1, 0, x, y1, 0], nn * 18);
      E.set([x, y0, 0.1, x2, y0, 0.1, x2, y0, 0.1, x2, y1, 0.1, x2, y1, 0.1, x, y1, 0.1, x, y1, 0.1, x, y0, 0.1], nn * 24);
      nn++;
    }
    d.fill.setDrawRange(0, nn * 6); d.edge.setDrawRange(0, nn * 8); d.seg.setDrawRange(0, nn * 2);
    [d.fill, d.edge, d.seg].forEach(g => { g.attributes.position.needsUpdate = true; });
    d.f.visible = d.e.visible = showSq && !!line;
  }

  const dots = new T.InstancedMesh(new T.CircleGeometry(1, 20), basic({}), MAXP); dots.frustumCulled = false; st.scene.add(dots);
  const ring = new T.InstancedMesh(new T.RingGeometry(0.75, 1, 20), basic({}), MAXP); ring.frustumCulled = false; st.scene.add(ring);
  const dummy = new T.Object3D();

  const outM = ctx.ui.readout({ label: 'Slope' }), outB = ctx.ui.readout({ label: 'Intercept' });
  const outS = ctx.ui.readout({ label: 'Sum of squared errors' }), outR = ctx.ui.readout({ label: 'R squared' });
  const outMine = ctx.ui.readout({ label: 'Your line: sum of squares' });
  const sse = (m, b) => pts.reduce((s, [x, y]) => s + (y - (m * x + b)) ** 2, 0);

  function update() {
    const n = pts.length; let mx = 0, my = 0; for (const [x, y] of pts) { mx += x; my += y; } mx /= n; my /= n;
    let sxx = 0, sxy = 0, syy = 0; for (const [x, y] of pts) { sxx += (x - mx) ** 2; sxy += (x - mx) * (y - my); syy += (y - my) ** 2; }
    fit = sxx > 1e-9 ? { m: sxy / sxx, b: my - (sxy / sxx) * mx } : null;
    const best = fit ? sse(fit.m, fit.b) : NaN;
    outM.set(fit ? fit.m.toFixed(3) : 'undefined'); outB.set(fit ? fit.b.toFixed(3) : 'undefined');
    outS.set(fit ? best.toFixed(3) : '—'); outR.set(fit && syy > 1e-9 ? (1 - best / syy).toFixed(3) : '—');
    fitLine.visible = !!fit; if (fit) setLine(fitLine, fit.m, fit.b, 0.07);
    fillDyn(dA, fit, 1);
    mineLine.visible = mine.on; if (mine.on) setLine(mineLine, mine.m, mine.b, 0.06);
    fillDyn(dB, mine.on ? mine : null, -1);
    if (mine.on) { const s = sse(mine.m, mine.b); outMine.set(s.toFixed(3) + (fit ? '  (' + (s - best >= -1e-9 ? '+' : '') + (s - best).toFixed(3) + ' above the minimum)' : '')); } else outMine.set('line hidden');
    const r = 0.17;
    pts.forEach(([x, y], i) => { dummy.position.set(x, y, 0.3); dummy.scale.set(r, r, 1); dummy.updateMatrix(); dots.setMatrixAt(i, dummy.matrix); dummy.position.z = 0.31; dummy.scale.set(r * 1.5, r * 1.5, 1); dummy.updateMatrix(); ring.setMatrixAt(i, dummy.matrix); });
    dots.count = ring.count = n; dots.instanceMatrix.needsUpdate = ring.instanceMatrix.needsUpdate = true;
    ctx.invalidate();
  }

  // dragging points
  let grab = -1;
  ctx.pointer(st.renderer.domElement, {
    down: (p) => {
      const { w, h } = half(), wx = p.x * w, wy = p.y * h; let bd = 0.8; grab = -1;
      pts.forEach(([x, y], i) => { const d = Math.hypot(x - wx, y - wy); if (d < bd) { bd = d; grab = i; } });
    },
    move: (p, down) => {
      if (!down || grab < 0) return; const { w, h } = half();
      pts[grab][0] = Math.max(-w + 0.25, Math.min(w - 0.25, p.x * w)); pts[grab][1] = Math.max(-h + 0.25, Math.min(h - 0.25, p.y * h)); update();
    },
    up: () => { grab = -1; },
  });

  ctx.ui.toggle({ label: 'Show squared errors', value: true, onChange: (v) => { showSq = v; update(); } });
  ctx.ui.button({ label: 'Add point', onClick: () => {
    if (pts.length >= MAXP) return; const { w } = half(); const x = (rnd() * 2 - 1) * (w - 0.8);
    const base = fit ? fit.m * x + fit.b : 0; pts.push([x, Math.max(-3.5, Math.min(3.5, base + (rnd() - 0.5) * 2.4))]); update();
  } });
  ctx.ui.button({ label: 'Reset', onClick: () => { pts = START.map(p => p.slice()); seed = 7; update(); } });
  const tog = ctx.ui.toggle({ label: 'Try my own line', value: false, onChange: (v) => { mine.on = v; sl1.el.style.display = sl2.el.style.display = v ? '' : 'none'; update(); } });
  const sl1 = ctx.ui.slider({ label: 'My slope', min: -3, max: 3, step: 0.01, value: mine.m, onInput: (v) => { mine.m = v; update(); } });
  const sl2 = ctx.ui.slider({ label: 'My intercept', min: -3, max: 3, step: 0.01, value: mine.b, onInput: (v) => { mine.b = v; update(); } });
  sl1.el.style.display = sl2.el.style.display = 'none';

  ctx.onTheme((p) => {
    axMat.color.set(p.rule); fitMat.color.set(p.c3); mineMat.color.set(p.c4);
    fillMatA.color.set(p.c3); lineMatA.color.set(p.c3); fillMatB.color.set(p.c4); lineMatB.color.set(p.c4);
    dots.material.color.set(p.ink); ring.material.color.set(p.paper);
  });
  update();
}
