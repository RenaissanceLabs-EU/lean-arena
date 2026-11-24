// PDE: a square membrane, 80 x 80 grid, fixed (zero) edges. Wave: u_tt = c^2 lap(u) - g u_t.  Heat: u_t = lap(u).
// Explicit schemes. Stability (h = grid spacing): wave needs c dt / h <= 1/sqrt(2) in 2D, we use 0.5.
// Heat needs dt <= h^2 / 4 (unit diffusivity), we use 0.2 h^2.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [0, 2.3, 2.5], target: [0, 0, 0.1], fov: 40, controls: false });
  st.scene.add(new T.AmbientLight(0xffffff, 1.3)); const sun = new T.DirectionalLight(0xffffff, 0.9); sun.position.set(1.5, 4, 2); st.scene.add(sun);
  const G = 80, h = 2 / (G - 1), C = 1, GAMMA = 0.25;
  const DTW = 0.5 * h / C, DTH = 0.2 * h * h, SPEEDW = 1.2, SPEEDH = 0.12; // simulated time per real second (heat is slowed so it can be watched)
  let mode = 'wave', acc = 0, pal = ctx.palette();
  let u = new Float32Array(G * G), up = new Float32Array(G * G), un = new Float32Array(G * G);
  const geo = new T.PlaneGeometry(2, 2, G - 1, G - 1); geo.rotateX(-Math.PI / 2);
  const P = geo.attributes.position; geo.setAttribute('color', new T.BufferAttribute(new Float32Array(G * G * 3), 3));
  const mat = new T.MeshStandardMaterial({ vertexColors: true, roughness: 0.6, metalness: 0.0, side: T.DoubleSide, flatShading: false });
  const mesh = new T.Mesh(geo, mat); st.scene.add(mesh);
  // PlaneGeometry vertex order: row j (z from -1 to 1), column i (x from -1 to 1): index j * G + i
  const edge = new T.LineSegments(new T.EdgesGeometry(new T.BoxGeometry(2, 0.0001, 2)), new T.LineBasicMaterial()); st.scene.add(edge);
  const colA = new T.Color(), colB = new T.Color(), colN = new T.Color(), col = new T.Color();
  const VS = 1.4; // display height per unit u
  function paint() {
    const cl = geo.attributes.color; let mx = 0;
    for (let k = 0; k < G * G; k++) {
      const v = u[k]; P.setY(k, v * VS); const a = Math.min(1, Math.sqrt(Math.abs(v)) * 1.8); mx = Math.max(mx, Math.abs(v));
      col.copy(colN).lerp(v >= 0 ? colA : colB, a); cl.setXYZ(k, col.r, col.g, col.b);
    }
    P.needsUpdate = true; cl.needsUpdate = true; geo.computeVertexNormals(); return mx;
  }
  const maxOut = ctx.ui.readout({ label: 'Largest height |u|' }), ruleOut = ctx.ui.readout({ label: 'Time step' });
  function stepWave() {
    const k2 = (C * DTW / h) ** 2, d = GAMMA * DTW / 2;
    for (let j = 1; j < G - 1; j++) for (let i = 1; i < G - 1; i++) {
      const k = j * G + i, lap = u[k - 1] + u[k + 1] + u[k - G] + u[k + G] - 4 * u[k];
      un[k] = (2 * u[k] - (1 - d) * up[k] + k2 * lap) / (1 + d);
    }
    const t = up; up = u; u = un; un = t;
  }
  function stepHeat() {
    const r = DTH / (h * h); // = 0.2 <= 1/4
    for (let j = 1; j < G - 1; j++) for (let i = 1; i < G - 1; i++) { const k = j * G + i; un[k] = u[k] + r * (u[k - 1] + u[k + 1] + u[k - G] + u[k + G] - 4 * u[k]); }
    const t = u; u = un; un = t;
  }
  function poke(x, z, amp) {
    const s2 = 2 * 0.09 * 0.09;
    for (let j = 1; j < G - 1; j++) for (let i = 1; i < G - 1; i++) {
      const dx = -1 + i * h - x, dz = -1 + j * h - z, b = amp * Math.exp(-(dx * dx + dz * dz) / s2); if (b < 1e-4) continue;
      const k = j * G + i; u[k] = Math.max(-1.5, Math.min(1.5, u[k] + b)); if (mode === 'wave') up[k] = Math.max(-1.5, Math.min(1.5, up[k] + b));
    }
  }
  function setMode(m) { mode = m; ruleOut.set(m === 'wave' ? 'c·dt/h = 0.50 (limit 0.707)' : 'dt/h² = 0.20 (limit 0.25)'); reset(); }
  function reset() { u.fill(0); up.fill(0); un.fill(0); poke(0, 0, 0.6); acc = 0; maxOut.set(paint().toFixed(3)); ctx.invalidate(); }
  ctx.ui.select({ label: 'Equation', options: [['wave', 'Wave equation (slightly damped)'], ['heat', 'Heat equation']], value: mode, onChange: setMode });
  ctx.ui.button({ label: 'Reset', onClick: reset });
  ctx.loop((dt) => {
    acc += dt * (mode === 'wave' ? SPEEDW : SPEEDH); const dts = mode === 'wave' ? DTW : DTH; let n = 0;
    while (acc >= dts && n < 300) { acc -= dts; if (mode === 'wave') stepWave(); else stepHeat(); n++; } if (acc > dts * 300) acc = 0;
    maxOut.set(paint().toFixed(3));
  });
  const ray = new T.Raycaster(), plane = new T.Plane(new T.Vector3(0, 1, 0), 0), hit = new T.Vector3(), nd = new T.Vector2();
  function pick(p, amp) {
    nd.set(p.x, p.y); ray.setFromCamera(nd, st.camera);
    if (ray.ray.intersectPlane(plane, hit) && Math.abs(hit.x) < 1 && Math.abs(hit.z) < 1) poke(hit.x, hit.z, amp);
  }
  ctx.pointer(st.renderer.domElement, { down: (p) => pick(p, 0.45), move: (p, down) => { if (down) pick(p, 0.12); } });
  ctx.onTheme((p) => { pal = p; colA.set(p.c3); colB.set(p.c4); colN.set(p.dark ? '#5a5d66' : '#f1ece0'); edge.material.color.set(p.ink); paint(); });
  setMode('wave');
}
