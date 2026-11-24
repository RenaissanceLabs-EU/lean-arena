// Mechanics: a planet on a Kepler ellipse. Time enters through M = n t; Kepler's equation M = E - e sin E fixes the position,
// so the planet speeds up near the star while equal-time wedges keep equal area.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [0, 7.6, 3.3], fov: 40 });
  if (st.controls) { st.controls.maxPolarAngle = 1.15; st.controls.minPolarAngle = 0.25; st.controls.minDistance = 4; }
  const A = 2.4, PERIOD = 12, DM = Math.PI / 5, TAU = 2 * Math.PI;
  let e = 0.6, M = 2.3, playing = !ctx.reduced;

  function solveE(m, ecc) { // Newton iteration on f(E) = E - e sin E - M, f' = 1 - e cos E >= 1 - e > 0
    m = ((m % TAU) + TAU) % TAU; let E = ecc < 0.8 ? m : Math.PI;
    for (let i = 0; i < 60; i++) { const d = (E - ecc * Math.sin(E) - m) / (1 - ecc * Math.cos(E)); E -= d; if (Math.abs(d) < 1e-13) break; }
    return E;
  }
  const bOf = () => A * Math.sqrt(1 - e * e);
  const pos = (E) => [A * Math.cos(E), -bOf() * Math.sin(E)]; // (x, z); star at (A e, 0)

  st.scene.add(new T.AmbientLight(0xffffff, 1));
  const orbitGeo = new T.BufferGeometry(); orbitGeo.setAttribute('position', new T.BufferAttribute(new Float32Array(200 * 3), 3));
  const orbitMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.8 });
  const orbit = new T.LineLoop(orbitGeo, orbitMat); orbit.frustumCulled = false; st.scene.add(orbit);
  const star = new T.Mesh(new T.SphereGeometry(0.22, 24, 16), new T.MeshBasicMaterial()); st.scene.add(star);
  const planet = new T.Mesh(new T.SphereGeometry(0.16, 24, 16), new T.MeshBasicMaterial()); st.scene.add(planet);
  const arrow = new T.ArrowHelper(new T.Vector3(1, 0, 0), new T.Vector3(), 1, 0xffffff, 0.2, 0.12); st.scene.add(arrow);

  const NW = 360;
  function wedge() {
    const g = new T.BufferGeometry(); g.setAttribute('position', new T.BufferAttribute(new Float32Array((NW + 2) * 3), 3));
    const idx = []; for (let i = 1; i <= NW; i++) idx.push(0, i, i + 1); g.setIndex(idx);
    const m = new T.Mesh(g, new T.MeshBasicMaterial({ transparent: true, opacity: 0.5, side: T.DoubleSide, depthWrite: false }));
    m.frustumCulled = false; st.scene.add(m); return m;
  }
  const wA = wedge(), wB = wedge();
  const lA = ctx.label('A', { size: 0.4, bold: true }), lB = ctx.label('B', { size: 0.4, bold: true }); st.scene.add(lA, lB);

  function fillWedge(w, m0, lab) { // returns the area in units of a^2 by summing the triangles star-P_i-P_{i+1}
    const P = w.geometry.attributes.position.array, sx = A * e; let area = 0, px = 0, pz = 0, mx = 0, mz = 0;
    P.set([sx, 0.02, 0], 0);
    for (let i = 0; i <= NW; i++) {
      const [x, z] = pos(solveE(m0 + DM * i / NW, e)); P.set([x, 0.02, z], (i + 1) * 3);
      const rx = x - sx;
      if (i > 0) area += 0.5 * Math.abs(px * z - pz * rx); // cross product of consecutive radius vectors from the star
      px = rx; pz = z; if (i === NW / 2) { mx = x; mz = z; }
    }
    w.geometry.attributes.position.needsUpdate = true;
    lab.position.set(sx + 0.78 * (mx - sx), 0.3, 0.78 * mz);
    return area / (A * A);
  }

  const outV = ctx.ui.readout({ label: 'Speed ÷ circular speed' }), outA = ctx.ui.readout({ label: 'Area of wedge A (area units a²)' }), outB = ctx.ui.readout({ label: 'Area of wedge B (area units a²)' });
  const outE = ctx.ui.readout({ label: 'Closest / farthest distance' });

  function shape() {
    const p = orbitGeo.attributes.position.array, b = bOf();
    for (let i = 0; i < 200; i++) { const a = i / 200 * TAU; p.set([A * Math.cos(a), 0, -b * Math.sin(a)], i * 3); }
    orbitGeo.attributes.position.needsUpdate = true; star.position.set(A * e, 0, 0);
    const aA = fillWedge(wA, -DM / 2, lA), aB = fillWedge(wB, Math.PI - DM / 2, lB);
    outA.set(aA.toFixed(4)); outB.set(aB.toFixed(4)); outE.set((1 - e).toFixed(2) + ' a  /  ' + (1 + e).toFixed(2) + ' a');
    place();
  }
  function place() {
    const E = solveE(M, e), [x, z] = pos(E), b = bOf(), r = A * (1 - e * Math.cos(E)); // distance from the star
    planet.position.set(x, 0, z);
    const ratio = Math.sqrt(2 * A / r - 1); // vis-viva: v^2 = GM (2/r - 1/a), circular speed^2 = GM/a
    const tx = -A * Math.sin(E), tz = -b * Math.cos(E), tl = Math.hypot(tx, tz);
    arrow.position.set(x, 0, z); arrow.setDirection(new T.Vector3(tx / tl, 0, tz / tl)); arrow.setLength(1.4 * ratio, 0.3, 0.16);
    outV.set(ratio.toFixed(2));
    ctx.invalidate();
  }

  ctx.ui.slider({ label: 'Eccentricity', min: 0, max: 0.9, step: 0.01, value: e, onInput: (v) => { e = v; shape(); } });
  const btn = ctx.ui.button({ label: playing ? 'Pause' : 'Play', onClick: () => { playing = !playing; btn.el.textContent = playing ? 'Pause' : 'Play'; } });
  ctx.loop((dt) => { if (playing) { M += TAU * dt / PERIOD; place(); } });

  ctx.onTheme((p) => {
    orbitMat.color.set(p.inkSoft); star.material.color.set(p.c1); planet.material.color.set(p.c2);
    wA.material.color.set(p.c3); wB.material.color.set(p.c4); arrow.setColor(p.ink);
    lA.userData.setColor(p.c3); lB.userData.setColor(p.c4);
  });
  shape();
}
