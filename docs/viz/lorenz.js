// Dynamical systems: the Lorenz system, two trajectories that start 1e-3 apart (RK4, fixed step 0.005).
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [1.8, 1.2, 8.6], target: [0, 0, 0], fov: 40 });
  const SIG = 10, BETA = 8 / 3, DT = 0.005, SAMPLE = 2, MAXP = 6000, SC = 0.08, SPEED = 3; // 3 time units per second of display
  let rho = 28, playing = !ctx.reduced, simT = 0, acc = 0, cnt = 0;
  const A = [1, 1, 1], B = [1.001, 1, 1], A0 = A.slice(), B0 = B.slice();
  const GN = 4000, ghostPos = new Float32Array(GN * 3), ghostGeo = new T.BufferGeometry();

  function deriv(x, y, z, o) { o[0] = SIG * (y - x); o[1] = x * (rho - z) - y; o[2] = x * y - BETA * z; }
  const k1 = [0, 0, 0], k2 = [0, 0, 0], k3 = [0, 0, 0], k4 = [0, 0, 0];
  function rk4(s) {
    deriv(s[0], s[1], s[2], k1);
    deriv(s[0] + DT / 2 * k1[0], s[1] + DT / 2 * k1[1], s[2] + DT / 2 * k1[2], k2);
    deriv(s[0] + DT / 2 * k2[0], s[1] + DT / 2 * k2[1], s[2] + DT / 2 * k2[2], k3);
    deriv(s[0] + DT * k3[0], s[1] + DT * k3[1], s[2] + DT * k3[2], k4);
    for (let i = 0; i < 3; i++) s[i] += DT / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]);
  }
  function mkTrail(color) {
    const geo = new T.BufferGeometry(); const pos = new Float32Array(MAXP * 3); geo.setAttribute('position', new T.BufferAttribute(pos, 3)); geo.setDrawRange(0, 0);
    const mat = new T.LineBasicMaterial({ color }); const line = new T.Line(geo, mat); line.frustumCulled = false; st.scene.add(line);
    const head = new T.Mesh(new T.SphereGeometry(color === '#b4862a' ? 0.09 : 0.06, 16, 12), new T.MeshBasicMaterial({ color })); st.scene.add(head);
    return { geo, pos, mat, head, n: 0 };
  }
  const tA = mkTrail('#b4862a'), tB = mkTrail('#2f7a7c');
  function push(tr, s) {
    const zc = rho - 1;
    if (tr.n === MAXP) { tr.pos.copyWithin(0, 3); tr.n--; }
    const o = tr.n * 3; tr.pos[o] = s[0] * SC; tr.pos[o + 1] = (s[2] - zc) * SC; tr.pos[o + 2] = s[1] * SC; tr.n++;
    tr.geo.setDrawRange(0, tr.n); tr.geo.attributes.position.needsUpdate = true; tr.head.position.set(s[0] * SC, (s[2] - zc) * SC, s[1] * SC);
  }
  ghostGeo.setAttribute('position', new T.BufferAttribute(ghostPos, 3));
  const ghostMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.3 }); const ghost = new T.Line(ghostGeo, ghostMat); ghost.frustumCulled = false; st.scene.add(ghost);
  const grid = new T.GridHelper(4, 8); grid.material.transparent = true; grid.material.opacity = 0.6; st.scene.add(grid);
  const sepOut = ctx.ui.readout({ label: 'Separation of the two trajectories' }), growOut = ctx.ui.readout({ label: 'Separation / initial separation' }), timeOut = ctx.ui.readout({ label: 'Model time' });
  function readout() {
    const s = Math.hypot(A[0] - B[0], A[1] - B[1], A[2] - B[2]), s0 = Math.hypot(A0[0] - B0[0], A0[1] - B0[1], A0[2] - B0[2]);
    sepOut.set(s.toExponential(2)); growOut.set('× ' + (s / s0 < 10 ? (s / s0).toFixed(2) : Math.round(s / s0).toLocaleString('en-US'))); timeOut.set(simT.toFixed(1));
  }
  function reset() {
    // start both on the attractor (after a 20 time-unit burn-in from (1,1,1)); the faint curve is one long orbit for context
    const w = [1, 1, 1]; for (let i = 0; i < 4000; i++) rk4(w);
    A0[0] = w[0]; A0[1] = w[1]; A0[2] = w[2]; B0[0] = w[0] + 1e-3; B0[1] = w[1]; B0[2] = w[2];
    for (let i = 0; i < GN; i++) { for (let k = 0; k < 3; k++) rk4(w); ghostPos[i * 3] = w[0] * SC; ghostPos[i * 3 + 1] = (w[2] - (rho - 1)) * SC; ghostPos[i * 3 + 2] = w[1] * SC; }
    ghostGeo.attributes.position.needsUpdate = true;
    for (let i = 0; i < 3; i++) { A[i] = A0[i]; B[i] = B0[i]; }
    simT = 0; acc = 0; cnt = 0; tA.n = 0; tB.n = 0; grid.position.y = -(rho - 1) * SC - 0.02; push(tA, A); push(tB, B); readout(); ctx.invalidate();
  }
  const rs = ctx.ui.slider({ label: 'Parameter ρ', min: 0, max: 40, step: 0.5, value: rho, format: (v) => v.toFixed(1), onInput: (v) => { rho = v; reset(); } });
  const pb = ctx.ui.button({ label: playing ? 'Pause' : 'Play', onClick: () => { playing = !playing; pb.el.textContent = playing ? 'Pause' : 'Play'; } });
  ctx.ui.button({ label: 'Reset', onClick: reset });
  ctx.loop((dt) => {
    if (!playing) return; acc += dt * SPEED;
    let guard = 0;
    while (acc >= DT && guard++ < 400) { acc -= DT; rk4(A); rk4(B); simT += DT; if (++cnt % SAMPLE === 0) { push(tA, A); push(tB, B); } }
    readout();
  });
  ctx.onTheme((p) => { tA.mat.color.set(p.c1); tA.head.material.color.set(p.c1); tB.mat.color.set(p.c2); tB.head.material.color.set(p.c2); grid.material.color.set(p.rule); ghostMat.color.set(p.ink); });
  reset();
}
