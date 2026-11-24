// Relativity: a light clock at rest next to the same clock moving at speed v, both seen from the rest frame.
// Light has speed c in this frame for both, so the moving pulse must cover a longer diagonal for each trip between mirrors.
// Geometry: in one tick of duration tau the clock moves v*c*tau sideways, the pulse rises L, and it travels c*tau in all:
//   (c tau)^2 = L^2 + (v c tau)^2.  We solve this for tau numerically (bisection) and compare with tau0 = L/c.
// The mirrors lie across the motion, so in this frame their width is contracted by 1/gamma; the gap L is not.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 3.8, pos: [0, 0, 10] });
  const L = 1.5, tau0 = 1.4, C = L / tau0, W = 0.8, Y0 = -1.0; // world units; one-way trip at rest takes tau0 seconds (slowed for viewing)
  let v = 0.8, time = 0, playing = !ctx.reduced, tau = tau0, X0 = 0, Xr = 0, Xend = 0, lastLayout = '';

  function solveTau(vv) { // c*tau = sqrt(L^2 + (v c tau)^2), bisection on f(t) = c t - sqrt(L^2 + (v c t)^2), increasing for t > 0
    let lo = 0, hi = tau0 * 100; const f = (t) => C * t - Math.hypot(L, vv * C * t);
    for (let i = 0; i < 80; i++) { const mid = (lo + hi) / 2; if (f(mid) < 0) lo = mid; else hi = mid; }
    return (lo + hi) / 2;
  }
  const tri = (u) => { const w = ((u % 2) + 2) % 2; return w < 1 ? w : 2 - w; };

  const mats = [];
  const bar = (w) => { const m = new T.MeshBasicMaterial(); mats.push(m); const o = new T.Mesh(new T.PlaneGeometry(w, 0.07), m); st.scene.add(o); return o; };
  const rb = [bar(W), bar(W)], mb = [bar(W), bar(W)];
  const pulseMat = new T.MeshBasicMaterial(), pulseM = new T.Mesh(new T.CircleGeometry(0.09, 20), pulseMat), pulseR = new T.Mesh(new T.CircleGeometry(0.09, 20), pulseMat);
  pulseM.position.z = pulseR.position.z = 0.2; st.scene.add(pulseM); st.scene.add(pulseR);
  const trailBuf = new Float32Array(40 * 3), trailGeo = new T.BufferGeometry(); trailGeo.setAttribute('position', new T.BufferAttribute(trailBuf, 3));
  const trailMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.85 }), trail = new T.Line(trailGeo, trailMat); trail.frustumCulled = false; st.scene.add(trail);
  const restLine = new T.Line(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute([0, 0, 0, 0, 0, 0], 3)), new T.LineBasicMaterial({ transparent: true, opacity: 0.3 }));
  const guideMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.25 });
  const guideR = new T.Line(new T.BufferGeometry().setAttribute('position', new T.BufferAttribute(new Float32Array(6), 3)), guideMat); st.scene.add(guideR);
  const lbR = ctx.label('At rest', { size: 0.26, bold: true }), lbM = ctx.label('', { size: 0.26, bold: true }), lbV = ctx.label('v →', { size: 0.24 });
  [lbR, lbM, lbV].forEach((l) => { l.position.z = 0.3; st.scene.add(l); });

  const gOut = ctx.ui.readout({ label: 'γ = 1/√(1−v²/c²)' }), pOut = ctx.ui.readout({ label: 'Path per tick ÷ L' }), tOut = ctx.ui.readout({ label: 'Tick lengths: moving ÷ rest' });
  const rOut = ctx.ui.readout({ label: 'Rest clock ticks' }), mOut = ctx.ui.readout({ label: 'Moving clock ticks' }), sOut = ctx.ui.readout({ label: 'In words' });
  const sv = ctx.ui.slider({ label: 'Speed v/c', min: 0, max: 0.99, step: 0.01, value: v, format: (x) => x.toFixed(2), onInput: (x) => { v = x; time = 0; setV(); } });
  const pb = ctx.ui.button({ label: playing ? 'Pause' : 'Play', onClick: () => { playing = !playing; pb.el.textContent = playing ? 'Pause' : 'Play'; } });
  ctx.ui.button({ label: 'Restart', onClick: () => { time = 0; frame(); } });

  function setV() {
    tau = solveTau(v); const g = 1 / Math.sqrt(1 - v * v); const path = Math.hypot(L, v * C * tau);
    gOut.set(g.toFixed(3)); pOut.set((path / L).toFixed(3)); tOut.set((tau / tau0).toFixed(3));
    sOut.set(v === 0 ? 'Both clocks tick together.' : 'The moving clock makes 1 tick while the rest clock makes ' + (tau / tau0).toFixed(2) + '.');
    lbM.userData.setText('Moving at ' + v.toFixed(2) + ' c'); const gw = 1 / g;
    mb.forEach((b) => b.scale.x = gw); lbV.visible = v > 0; frame();
  }
  const pt = (t, q, Lc) => [X0 + v * C * t - q * Lc, Y0 + L * tri(t / tau)];
  function frame() {
    const { w, h } = ctx.size(); const hw = st.height / 2 * w / h;
    Xr = -hw + 0.75; X0 = Xr + 1.15; Xend = Math.min(hw - 0.45, X0 + 4.2); const Lc = Math.max(1.2, Xend - X0);
    const s = v * C * time, q = v > 0 ? Math.floor(s / Lc) : 0, tw = v > 0 ? q * Lc / (v * C) : 0;
    // rest clock
    rb[0].position.set(Xr, Y0, 0); rb[1].position.set(Xr, Y0 + L, 0); pulseR.position.set(Xr, Y0 + L * tri(time / tau0), 0.2);
    const g = restLine.geometry.attributes.position; g.array.set([Xr, Y0, 0, Xr, Y0 + L, 0]); g.needsUpdate = true;
    // moving clock (mirror centres follow the pulse's x)
    const [px, py] = pt(time, q, Lc); mb[0].position.set(px, Y0, 0); mb[1].position.set(px, Y0 + L, 0); pulseM.position.set(px, py, 0.2);
    guideR.geometry.attributes.position.array.set([px, Y0, 0, px, Y0 + L, 0]); guideR.geometry.attributes.position.needsUpdate = true;
    // zigzag trail within the current sweep: start of sweep, each bounce since, then now
    const pts = []; const kNow = Math.floor(time / tau); const tStart = Math.max(tw, (kNow - 11) * tau);
    pts.push(pt(tStart, q, Lc)); for (let k = Math.floor(tStart / tau) + 1; k <= kNow; k++) if (k * tau > tStart) pts.push(pt(k * tau, q, Lc)); pts.push([px, py]);
    pts.forEach((p, i) => { trailBuf[i * 3] = p[0]; trailBuf[i * 3 + 1] = p[1]; trailBuf[i * 3 + 2] = 0.1; }); trailGeo.setDrawRange(0, pts.length); trailGeo.attributes.position.needsUpdate = true;
    lbR.position.set(Xr, Y0 + L + 0.38, 0.3); lbM.position.set(Math.min(Math.max(px, X0), Xend - 0.6), Y0 + L + 0.38, 0.3); lbV.position.set(px, Y0 - 0.3, 0.3);
    rOut.set(String(Math.floor(time / tau0 + 1e-9))); mOut.set(String(Math.floor(time / tau + 1e-9)));
    ctx.invalidate();
  }
  ctx.loop((dt) => { if (playing) { time += dt; } frame(); });

  ctx.onTheme((p) => {
    mats.forEach((m) => m.color.set(p.ink)); pulseMat.color.set(p.c1); trailMat.color.set(p.c1); guideMat.color.set(p.inkSoft); restLine.material.color.set(p.inkSoft);
    [lbR, lbM, lbV].forEach((l) => l.userData.setColor(p.ink));
  });
  setV();
}
