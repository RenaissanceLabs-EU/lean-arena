// Manifolds: the Mobius strip X(u,s) = ((R + s cos(u/2)) cos u, (R + s cos(u/2)) sin u, s sin(u/2)), u in [0, 2pi], s in [-w, w].
// Note X(u + 2pi, s) = X(u, -s). A normal arrow carried continuously along the center line (s = 0) returns reversed after one lap.
// Cutting along s = 0 leaves one band: u runs over [0, 4pi] and s over [0, w] (the second lap covers the other half).
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [0.5, 3.1, 4.6], fov: 38 });
  st.scene.add(new T.AmbientLight(0xffffff, 1.0)); const sun = new T.DirectionalLight(0xffffff, 1.2); sun.position.set(3, 5, 4); st.scene.add(sun); const sun2 = new T.DirectionalLight(0xffffff, 0.8); sun2.position.set(-2, -5, -3); st.scene.add(sun2);
  const R = 1.25, W = 0.5, G = 0.13, TP = Math.PI * 2;
  const sin = Math.sin, cos = Math.cos;
  function X(u, s) { const r = R + s * cos(u / 2); return [r * cos(u), r * sin(u), s * sin(u / 2)]; }
  function Nrm(u, s) {
    const c = cos(u / 2), sn = sin(u / 2), cu = cos(u), su = sin(u), r = R + s * c;
    const xs = [c * cu, c * su, sn], xu = [-r * su - 0.5 * s * sn * cu, r * cu - 0.5 * s * sn * su, 0.5 * s * c];
    const n = [xs[1] * xu[2] - xs[2] * xu[1], xs[2] * xu[0] - xs[0] * xu[2], xs[0] * xu[1] - xs[1] * xu[0]]; const l = Math.hypot(...n); return [n[0] / l, n[1] / l, n[2] / l];
  }
  const V3 = (a) => new T.Vector3(a[0], a[2], a[1]); // scene coords: (x, y, z) -> (x, z, y)
  const stripMat = new T.MeshStandardMaterial({ side: T.DoubleSide, roughness: 0.5, metalness: 0.02 });
  const strip = new T.Mesh(new T.BufferGeometry(), stripMat); st.scene.add(strip);
  const edgeMat = new T.MeshBasicMaterial(), cutMat = new T.MeshBasicMaterial();
  const edge = new T.Mesh(new T.BufferGeometry(), edgeMat), cutLine = new T.Mesh(new T.BufferGeometry(), cutMat); st.scene.add(edge, cutLine);
  const marker = new T.Mesh(new T.SphereGeometry(0.07, 16, 12), new T.MeshBasicMaterial()); st.scene.add(marker);
  const mkArrow = (len) => { const a = new T.ArrowHelper(new T.Vector3(0, 1, 0), new T.Vector3(), len, 0xffffff, 0.16, 0.1); [a.line.material, a.cone.material].forEach(m => { m.depthTest = false; }); a.renderOrder = 6; a.line.renderOrder = a.cone.renderOrder = 6; st.scene.add(a); return a; };
  const arrowNow = mkArrow(0.7), arrowStart = mkArrow(0.5);

  let cutOn = false, cutAmt = 0, laps = 1, playing = false;
  const tube = (u0, u1, s, n) => { const pts = []; for (let k = 0; k <= n; k++) pts.push(V3(X(u0 + (u1 - u0) * k / n, s))); return new T.TubeGeometry(new T.CatmullRomCurve3(pts), n, 0.014, 5); };
  function buildStrip() {
    const g0 = G * cutAmt, longer = cutAmt > 0, u1 = longer ? 2 * TP : TP, s0 = longer ? g0 : -W, s1 = W;
    const nu = longer ? 240 : 120, ns = 8, pos = [], idx = [];
    for (let i = 0; i <= nu; i++) for (let j = 0; j <= ns; j++) { const p = V3(X(u1 * i / nu, s0 + (s1 - s0) * j / ns)); pos.push(p.x, p.y, p.z); }
    for (let i = 0; i < nu; i++) for (let j = 0; j < ns; j++) { const a = i * (ns + 1) + j; idx.push(a, a + 1, a + ns + 1, a + 1, a + ns + 2, a + ns + 1); }
    strip.geometry.dispose(); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals(); strip.geometry = g;
    edge.geometry.dispose(); edge.geometry = tube(0, 2 * TP, W, 360); // the single boundary curve of the strip: s = w, u over [0, 4pi]
    cutLine.geometry.dispose(); cutLine.geometry = tube(0, longer ? 2 * TP : TP, g0, longer ? 360 : 180);
  }
  const lapOut = ctx.ui.readout({ label: 'Laps walked' }), arrOut = ctx.ui.readout({ label: 'Arrow compared with its start' }), edOut = ctx.ui.readout({ label: 'Boundary curves / pieces' }), lenOut = ctx.ui.readout({ label: 'Band length' });
  function place() {
    const sm = cutAmt * (G * cutAmt + W) / 2, u = laps * TP, p = V3(X(u, sm)), n = V3(Nrm(u, sm)), p0 = V3(X(0, sm)), n0 = V3(Nrm(0, sm));
    marker.position.copy(p); arrowNow.position.copy(p); arrowNow.setDirection(n); arrowStart.position.copy(p0); arrowStart.setDirection(n0);
    const dot = Math.max(-1, Math.min(1, n.dot(n0))), ang = Math.acos(dot) * 180 / Math.PI, back = p.distanceTo(p0) < 1e-6;
    lapOut.set(laps.toFixed(2));
    arrOut.set((back ? 'same point; ' : 'different point; ') + (dot < -0.9999 ? 'arrow reversed (180°)' : dot > 0.9999 ? 'arrow the same' : 'angle between them ' + ang.toFixed(0) + '°'));
    edOut.set(cutOn ? '2 boundary curves, 1 piece' : '1 boundary curve, 1 piece'); lenOut.set(cutOn ? '2x the original length, half the width, one full twist' : '1x: one half twist');
  }
  const lapSl = ctx.ui.slider({ label: 'Walk along the strip (laps)', min: 0, max: 2, step: 0.01, value: laps, onInput: (v) => { laps = v; place(); } });
  ctx.ui.toggle({ label: 'Cut along the middle', value: false, onChange: (v) => { cutOn = v; place(); } });
  ctx.ui.button({ label: 'Walk', onClick: () => { playing = true; if (laps >= 1.995) { laps = 0; } } });
  ctx.loop((dt) => {
    const tgt = cutOn ? 1 : 0;
    if (Math.abs(cutAmt - tgt) > 1e-4) { cutAmt += Math.sign(tgt - cutAmt) * Math.min(Math.abs(tgt - cutAmt), dt / 1.2); buildStrip(); place(); }
    if (playing) { laps = Math.min(2, laps + dt / 6); lapSl.set(laps); if (laps >= 2) playing = false; }
  });
  ctx.onTheme((p) => {
    stripMat.color.set(p.c2); stripMat.emissive.set(p.c2); stripMat.emissiveIntensity = 0.4; edgeMat.color.set(p.ink); cutMat.color.set(p.c3); marker.material.color.set(p.c1);
    arrowNow.setColor(p.c1); arrowStart.setColor(p.c4);
  });
  buildStrip(); place();
}
