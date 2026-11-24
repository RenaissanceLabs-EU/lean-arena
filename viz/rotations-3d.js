// Lie groups: 3D rotations do not commute. The same moves are applied in the order pressed (left) and in reverse order (right).
// Orientation is tracked with exact integer rotation matrices; the animation is only a display of those matrices.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [1.6, 3.2, 6.6], fov: 38 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.85)); const sun = new T.DirectionalLight(0xffffff, 1.2); sun.position.set(3, 5, 6); st.scene.add(sun);

  const I3 = [1, 0, 0, 0, 1, 0, 0, 0, 1];
  const RX = [1, 0, 0, 0, 0, -1, 0, 1, 0], RY = [0, 0, 1, 0, 1, 0, -1, 0, 0]; // +90 degrees about x and about y (right-handed)
  const mul = (A, B) => { const C = new Array(9); for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) C[i * 3 + j] = A[i * 3] * B[j] + A[i * 3 + 1] * B[3 + j] + A[i * 3 + 2] * B[6 + j]; return C; };
  const tr = (A) => A[0] + A[4] + A[8], tp = (A) => [A[0], A[3], A[6], A[1], A[4], A[7], A[2], A[5], A[8]];
  const M4 = (A) => new T.Matrix4().set(A[0], A[1], A[2], 0, A[3], A[4], A[5], 0, A[6], A[7], A[8], 0, 0, 0, 0, 1);
  const MV = { x: { m: RX, ax: new T.Vector3(1, 0, 0) }, y: { m: RY, ax: new T.Vector3(0, 1, 0) } };

  function faceTex(txt, bg, fg) {
    const c = document.createElement('canvas'); c.width = c.height = 128; const g = c.getContext('2d');
    g.fillStyle = bg; g.fillRect(0, 0, 128, 128); g.strokeStyle = 'rgba(0,0,0,0.35)'; g.lineWidth = 6; g.strokeRect(3, 3, 122, 122);
    g.fillStyle = fg; g.font = '600 88px sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(txt, 64, 70);
    const t = new T.CanvasTexture(c); t.colorSpace = T.SRGBColorSpace; return t;
  }
  const faces = [['+x', '#c0504d', '#fff'], ['−x', '#e3aaa6', '#222'], ['+y', '#6f8f22', '#fff'], ['−y', '#c3d58a', '#222'], ['+z', '#3f5fa8', '#fff'], ['−z', '#9db0dc', '#222']];
  const mats = faces.map(f => new T.MeshStandardMaterial({ map: faceTex(f[0], f[1], f[2]), roughness: 0.6 }));
  const boxGeo = new T.BoxGeometry(1.45, 0.95, 0.65);

  const arrowCols = ['c3', 'c5', 'c4'], arrows = [];
  function makeCopy(px, title) {
    const root = new T.Group(); root.position.x = px; st.scene.add(root);
    const body = new T.Group(); root.add(body); body.add(new T.Mesh(boxGeo, mats));
    body.add(new T.LineSegments(new T.EdgesGeometry(boxGeo), new T.LineBasicMaterial({ color: 0x222222 })));
    [[1, 0, 0], [0, 1, 0], [0, 0, 1]].forEach((d, k) => { const a = new T.ArrowHelper(new T.Vector3(...d), new T.Vector3(), 1.25, 0xffffff, 0.22, 0.14); root.add(a); arrows.push([a, k]); });
    const lab = ctx.label(title, { size: 0.36, bold: true }); lab.position.set(0, 1.45, 0); root.add(lab);
    return { body, lab, M: I3.slice(), settled: new T.Quaternion(), queue: [], t: 0 };
  }
  const L = makeCopy(-1.5, 'x, y'), R = makeCopy(1.5, 'y, x');
  const axl = [['x', 0], ['y', 1], ['z', 2]];
  let seq = [];

  function setInstant(c, moves) { c.M = I3.slice(); moves.forEach(k => { c.M = mul(MV[k].m, c.M); }); c.settled.setFromRotationMatrix(M4(c.M)); c.body.quaternion.copy(c.settled); c.queue = []; c.t = 0; }
  function press(k) {
    if (seq.length >= 6) return; seq.push(k); L.queue.push(k);
    R.M = I3.slice(); R.settled.identity(); R.body.quaternion.identity(); R.queue = seq.slice().reverse(); R.t = 0;
    if (ctx.reduced) { setInstant(L, seq); setInstant(R, seq.slice().reverse()); }
    status();
  }
  const seqOut = ctx.ui.readout({ label: 'Moves, in the order pressed' }), cmpOut = ctx.ui.readout({ label: 'Final orientations' });
  const qa = new T.Quaternion();
  function status() {
    L.lab.userData.setText(seq.length ? seq.join(', ') : 'start'); R.lab.userData.setText(seq.length ? seq.slice().reverse().join(', ') : 'start');
    seqOut.set(seq.length ? seq.join(', then ') + '  (each 90° about a fixed axis)' : 'none yet');
    if (L.queue.length || R.queue.length) { cmpOut.set('turning…'); return; }
    let A = I3, B = I3; seq.forEach(k => { A = mul(MV[k].m, A); }); seq.slice().reverse().forEach(k => { B = mul(MV[k].m, B); });
    const D = mul(A, tp(B)); // rotation taking one final pose to the other
    const same = D.every((v, i) => v === I3[i]);
    if (same) cmpOut.set('identical: these moves commute');
    else cmpOut.set('different: they differ by a rotation of ' + Math.round(Math.acos(Math.max(-1, Math.min(1, (tr(D) - 1) / 2))) * 180 / Math.PI) + '°');
  }
  function step(c, dt) {
    if (!c.queue.length) return false;
    const k = c.queue[0]; c.t = Math.min(1, c.t + dt / 0.8);
    const e = c.t * c.t * (3 - 2 * c.t);
    qa.setFromAxisAngle(MV[k].ax, e * Math.PI / 2); c.body.quaternion.copy(qa).multiply(c.settled);
    if (c.t >= 1) { c.M = mul(MV[k].m, c.M); c.settled.setFromRotationMatrix(M4(c.M)); c.body.quaternion.copy(c.settled); c.queue.shift(); c.t = 0; return true; }
    return false;
  }
  ctx.ui.button({ label: 'Rotate 90° about x', onClick: () => press('x') });
  ctx.ui.button({ label: 'Rotate 90° about y', onClick: () => press('y') });
  ctx.ui.button({ label: 'Reset', onClick: () => { seq = []; setInstant(L, []); setInstant(R, []); status(); } });
  ctx.loop((dt) => { const a = step(L, dt), b = step(R, dt); if (a || b) status(); });

  ctx.onTheme((p) => { arrows.forEach(([a, k]) => a.setColor(p[arrowCols[k]])); L.lab.userData.setColor(p.ink); R.lab.userData.setColor(p.ink); });
  seq = ['x', 'y']; setInstant(L, seq); setInstant(R, ['y', 'x']); status();
}
