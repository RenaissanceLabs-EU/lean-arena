// Calculus of variations: a soap film between two coaxial rings of radius R = 1 (lengths in units of R).
// A film of revolution that is minimal has r(z) = a cosh(z/a). Requiring r(+-s) = 1 with s = h/(2R) gives
//   cosh(u)/u = 1/s  with u = s/a.   The left side has its minimum 1.50888 at u0 (u0 tanh u0 = 1), so a solution exists only for
//   s <= 1/1.50888, i.e. h/R <= 1.3255; below that there are two: u < u0 (large a, stable) and u > u0 (small a, unstable).
// Area of the catenoid: A = pi a (2s + a sinh(2s/a)); two flat discs: 2 pi.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [2.8, 1.8, 3.6], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.9)); const sun = new T.DirectionalLight(0xffffff, 1.2); sun.position.set(3, 5, 4); st.scene.add(sun);
  const g = (u) => Math.cosh(u) / u;
  let u0 = 1; for (let i = 0; i < 80; i++) { /* u tanh u = 1 by Newton */ u0 -= (u0 * Math.tanh(u0) - 1) / (Math.tanh(u0) + u0 / Math.cosh(u0) ** 2); }
  const sCrit = 1 / g(u0), HC = 2 * sCrit;
  function neck(s) { // returns { a, aUnstable } or null if no catenoid
    if (s > sCrit) return null; if (s >= sCrit - 1e-12) return { a: s / u0, a2: s / u0 };
    let lo = 1e-9, hi = u0; for (let i = 0; i < 100; i++) { const m = (lo + hi) / 2; if (g(m) > 1 / s) lo = m; else hi = m; } // g decreasing on (0, u0]
    const u1 = (lo + hi) / 2; lo = u0; hi = 60; for (let i = 0; i < 100; i++) { const m = (lo + hi) / 2; if (g(m) < 1 / s) lo = m; else hi = m; } // g increasing beyond u0
    return { a: s / u1, a2: s / ((lo + hi) / 2) };
  }
  const area = (a, s) => Math.PI * a * (2 * s + a * Math.sinh(2 * s / a));
  let lo = 0.3 / 2, hi = sCrit; for (let i = 0; i < 100; i++) { const m = (lo + hi) / 2; if (area(neck(m).a, m) < 2 * Math.PI) lo = m; else hi = m; }
  const HG = 2 * (lo + hi) / 2; // separation where the catenoid area equals the discs' area

  const filmMat = new T.MeshStandardMaterial({ transparent: true, opacity: 0.55, side: T.DoubleSide, roughness: 0.3, depthWrite: false });
  const lineMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.6 }), ringMat = new T.MeshStandardMaterial({ roughness: 0.4 });
  const filmGrp = new T.Group(); st.scene.add(filmGrp);
  let filmMesh = null, lines = null;
  const rings = [0, 1].map(() => { const m = new T.Mesh(new T.TorusGeometry(1, 0.03, 12, 96), ringMat); m.rotation.x = Math.PI / 2; st.scene.add(m); return m; });
  const NM = 18, NZ = 48, NP = 10, NT = 72;
  function build(s, a) { // surface of revolution (a > 0) or two flat discs (a = 0)
    if (filmMesh) { filmGrp.remove(filmMesh); filmMesh.geometry.dispose(); }
    if (lines) { filmGrp.remove(lines); lines.geometry.dispose(); }
    const pos = [];
    const seg = (x0, y0, z0, x1, y1, z1) => pos.push(x0, y0, z0, x1, y1, z1);
    if (a > 0) {
      const pts = []; for (let i = 0; i <= NZ; i++) { const z = -s + 2 * s * i / NZ; pts.push(new T.Vector2(a * Math.cosh(z / a), z)); }
      filmMesh = new T.Mesh(new T.LatheGeometry(pts, NT), filmMat);
      for (let j = 0; j < NM; j++) { const t = j / NM * Math.PI * 2; for (let i = 0; i < NZ; i++) seg(pts[i].x * Math.sin(t), pts[i].y, pts[i].x * Math.cos(t), pts[i + 1].x * Math.sin(t), pts[i + 1].y, pts[i + 1].x * Math.cos(t)); }
      for (let k = 0; k <= NP; k++) { const i = Math.round(k / NP * NZ), r = pts[i].x, y = pts[i].y; for (let j = 0; j < NT; j++) { const t0 = j / NT * Math.PI * 2, t1 = (j + 1) / NT * Math.PI * 2; seg(r * Math.sin(t0), y, r * Math.cos(t0), r * Math.sin(t1), y, r * Math.cos(t1)); } }
    } else {
      const grp = new T.Group(); [-s, s].forEach((y) => { const d = new T.Mesh(new T.CircleGeometry(1, NT), filmMat); d.rotation.x = -Math.PI / 2; d.position.y = y; grp.add(d); });
      filmMesh = grp; grp.geometry = { dispose() {} };
      [-s, s].forEach((y) => { for (let j = 0; j < NM; j++) { const t = j / NM * Math.PI * 2; seg(0, y, 0, Math.sin(t), y, Math.cos(t)); }
        for (let k = 1; k <= 4; k++) for (let j = 0; j < NT; j++) { const t0 = j / NT * Math.PI * 2, t1 = (j + 1) / NT * Math.PI * 2, r = k / 4; seg(r * Math.sin(t0), y, r * Math.cos(t0), r * Math.sin(t1), y, r * Math.cos(t1)); } });
    }
    lines = new T.LineSegments(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(pos, 3)), lineMat);
    filmGrp.add(filmMesh); filmGrp.add(lines);
  }

  const aOut = ctx.ui.readout({ label: 'Neck radius a/R' }), arOut = ctx.ui.readout({ label: 'Film area ÷ two discs' }), stOut = ctx.ui.readout({ label: 'State' });
  ctx.ui.readout({ label: 'Marks on slider', value: 'gold ' + HG.toFixed(3) + ' (discs smaller beyond), red ' + HC.toFixed(4) + ' (no film beyond)' });
  let pal = ctx.palette();
  function update(H) {
    const s = H / 2, n = neck(s);
    rings[0].position.y = -s; rings[1].position.y = s;
    if (n) {
      build(s, n.a); const A = area(n.a, s), ratio = A / (2 * Math.PI);
      aOut.set(n.a.toFixed(3) + '  (unstable branch: ' + n.a2.toFixed(3) + ')'); arOut.set(ratio.toFixed(3));
      const smaller = ratio > 1; filmMat.color.set(smaller ? pal.c1 : pal.c2);
      stOut.set(smaller ? 'Film exists, but the discs have less area: it can jump' : 'Film is the least-area surface');
    } else {
      build(s, 0); filmMat.color.set(pal.c3); aOut.set('none: no catenoid fits'); arOut.set('1.000  (two discs)'); stOut.set('The film has broken into two discs');
    }
    ctx.invalidate();
  }
  const sl = ctx.ui.slider({ label: 'Ring separation h/R', min: 0.05, max: 1.8, step: 0.01, value: 1.0, format: (v) => v.toFixed(2), onInput: update });
  // markers on the slider range: area crossover (gold) and critical separation (red)
  const wrap = sl.el, input = wrap.querySelector('input'); wrap.style.position = 'relative'; const marks = [];
  [[HG, 'gold'], [HC, 'red']].forEach(([val, key]) => { const m = document.createElement('i'); m.style.cssText = 'position:absolute;width:3px;height:16px;border-radius:2px;pointer-events:none;top:50%;margin-top:-8px;'; m.title = key === 'gold' ? 'Above this, two discs have less area' : 'Above this, no film exists'; wrap.append(m); marks.push([m, val, key]); });
  const place = () => { marks.forEach(([m, val]) => { m.style.left = (input.offsetLeft + 8 + (val - 0.05) / (1.8 - 0.05) * (input.offsetWidth - 16) - 1.5) + 'px'; }); };
  new ResizeObserver(place).observe(wrap); place();
  ctx.onTheme((p) => {
    pal = p; lineMat.color.set(p.dark ? '#cfd6e0' : '#35404d'); ringMat.color.set(p.ink); marks.forEach(([m, , key]) => { m.style.background = key === 'gold' ? p.c1 : p.c3; });
    update(sl.get());
  });
}
