// Linear algebra: what a matrix does to space. A cube and a sphere are carried from the identity to M.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [2.9, 2.2, 3.7], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.8)); const sun = new T.DirectionalLight(0xffffff, 1.4); sun.position.set(3, 5, 4); st.scene.add(sun);
  const grp = new T.Group(); st.scene.add(grp);

  const presets = {
    rotate:  { name: 'Rotation', m: (() => { const a = 1.0, c = Math.cos(a), s = Math.sin(a); return [c, 0, s, 0, 1, 0, -s, 0, c]; })() },
    scale:   { name: 'Stretch', m: [1.7, 0, 0, 0, 0.6, 0, 0, 0, 1.2] },
    shear:   { name: 'Shear', m: [1, 0.9, 0, 0, 1, 0, 0, 0, 1] },
    flip:    { name: 'Reflection', m: [-1, 0, 0, 0, 1, 0, 0, 0, 1] },
    project: { name: 'Projection (flattens)', m: [1, 0, 0, 0, 1, 0, 0, 0, 0] },
    mixed:   { name: 'A general matrix', m: [1.2, 0.5, 0, -0.4, 0.9, 0.3, 0.2, 0, 1.3] },
  };
  let cur = presets.rotate.m, tval = 1;

  // geometry: sphere (points on a wire sphere) and a cube frame, built once and re-transformed on the CPU
  const sph = new T.SphereGeometry(1, 40, 28); const base = sph.attributes.position.array.slice();
  const sphereMat = new T.MeshStandardMaterial({ transparent: true, opacity: 0.55, roughness: 0.35, metalness: 0.05, depthWrite: false });
  const sphereMesh = new T.Mesh(sph, sphereMat); grp.add(sphereMesh);
  // latitude and longitude rings only: far less visual noise than a triangle wireframe
  const ringPts = []; const N = 64;
  for (let k = -2; k <= 2; k++) { const lat = (k / 3) * Math.PI / 2 * 1.0, r = Math.cos(lat), y = Math.sin(lat); for (let i = 0; i < N; i++) { const a = i / N * Math.PI * 2, b = (i + 1) / N * Math.PI * 2; ringPts.push(r * Math.cos(a), y, r * Math.sin(a), r * Math.cos(b), y, r * Math.sin(b)); } }
  for (let k = 0; k < 6; k++) { const lon = k / 6 * Math.PI; for (let i = 0; i < N; i++) { const a = i / N * Math.PI * 2, b = (i + 1) / N * Math.PI * 2;
    ringPts.push(Math.cos(a) * Math.cos(lon), Math.sin(a), Math.cos(a) * Math.sin(lon), Math.cos(b) * Math.cos(lon), Math.sin(b), Math.cos(b) * Math.sin(lon)); } }
  const wireMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.85 });
  const wireGeo = new T.BufferGeometry(); wireGeo.setAttribute('position', new T.Float32BufferAttribute(ringPts, 3));
  const wire = new T.LineSegments(wireGeo, wireMat); grp.add(wire);
  const wireBase = wire.geometry.attributes.position.array.slice();
  const cubeGeo = new T.BoxGeometry(1.4, 1.4, 1.4); const cubeBase = new T.EdgesGeometry(cubeGeo).attributes.position.array.slice();
  const cubeEdges = new T.LineSegments(new T.EdgesGeometry(cubeGeo), new T.LineBasicMaterial()); grp.add(cubeEdges);
  const arrows = [0, 1, 2].map(() => new T.ArrowHelper(new T.Vector3(1, 0, 0), new T.Vector3(), 1, 0xffffff, 0.18, 0.1));
  arrows.forEach(a => grp.add(a));
  const grid = new T.GridHelper(6, 12); grid.position.y = -1.9; st.scene.add(grid);

  const M = new T.Matrix3();
  function blend() { // (1-t) I + t M
    const I = [1, 0, 0, 0, 1, 0, 0, 0, 1]; return I.map((v, i) => (1 - tval) * v + tval * cur[i]);
  }
  function apply(src, dst, m) {
    for (let i = 0; i < src.length; i += 3) {
      const x = src[i], y = src[i + 1], z = src[i + 2];
      dst[i] = m[0] * x + m[1] * y + m[2] * z; dst[i + 1] = m[3] * x + m[4] * y + m[5] * z; dst[i + 2] = m[6] * x + m[7] * y + m[8] * z;
    }
  }
  const det3 = (m) => m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6]) + m[2] * (m[3] * m[7] - m[4] * m[6]);
  function rank3(m) {
    const a = [m.slice(0, 3), m.slice(3, 6), m.slice(6, 9)]; let r = 0;
    for (let c = 0; c < 3 && r < 3; c++) {
      let p = r; for (let i = r + 1; i < 3; i++) if (Math.abs(a[i][c]) > Math.abs(a[p][c])) p = i;
      if (Math.abs(a[p][c]) < 1e-6) continue; [a[r], a[p]] = [a[p], a[r]];
      for (let i = r + 1; i < 3; i++) { const f = a[i][c] / a[r][c]; for (let k = c; k < 3; k++) a[i][k] -= f * a[r][k]; } r++;
    } return r;
  }
  const detOut = ctx.ui.readout({ label: 'Volume scale (determinant)' });
  const rankOut = ctx.ui.readout({ label: 'Dimension of the image (rank)' });
  function update() {
    const m = blend();
    const p = sph.attributes.position; apply(base, p.array, m); p.needsUpdate = true; sph.computeVertexNormals();
    const w = wire.geometry.attributes.position; apply(wireBase, w.array, m); w.needsUpdate = true;
    const c = cubeEdges.geometry.attributes.position; apply(cubeBase, c.array, m); c.needsUpdate = true;
    [[1, 0, 0], [0, 1, 0], [0, 0, 1]].forEach((e, k) => {
      const v = new T.Vector3(m[0 + k], m[3 + k], m[6 + k]); const len = v.length();
      arrows[k].visible = len > 1e-3; if (len > 1e-3) { arrows[k].setDirection(v.clone().normalize()); arrows[k].setLength(len * 1.0, 0.18, 0.1); }
    });
    const d = det3(m); detOut.set((d >= 0 ? '' : '−') + Math.abs(d).toFixed(2) + (d < -1e-6 ? '  (orientation flipped)' : ''));
    rankOut.set(String(rank3(m)));
  }

  ctx.ui.select({ label: 'Matrix', options: Object.entries(presets).map(([k, v]) => [k, v.name]), value: 'rotate', onChange: (k) => { cur = presets[k].m; slider.set(1); } });
  const slider = ctx.ui.slider({ label: 'From identity to M', min: 0, max: 1, step: 0.01, value: 1, onInput: (v) => { tval = v; update(); } });
  ctx.ui.button({ label: 'Play', onClick: () => { play = true; phase = 0; } });
  let play = false, phase = 0;
  ctx.loop((dt) => { if (play) { phase += dt * 0.5; const v = 0.5 - 0.5 * Math.cos(phase * Math.PI * 2); tval = v; slider.set(v); if (phase >= 1) { play = false; slider.set(1); } } });

  ctx.onTheme((p) => {
    sphereMat.color.set(p.c2); wireMat.color.set(p.dark ? '#9fd6d8' : '#1f5c5e'); cubeEdges.material.color.set(p.ink);
    arrows[0].setColor(p.c3); arrows[1].setColor(p.c5); arrows[2].setColor(p.c4);
    grid.material.color.set(p.rule); grid.material.transparent = true; grid.material.opacity = 0.6;
  });
  update();
}
