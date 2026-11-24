// Group theory: two rotations of a cube generate its whole rotation group (24 elements).
// The orientation is an exact integer rotation matrix; every move is a left-multiplication by a fixed-axis rotation.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [3.4, 3.0, 5.0], fov: 38 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.85)); const sun = new T.DirectionalLight(0xffffff, 1.2); sun.position.set(3, 5, 6); st.scene.add(sun);

  const I3 = [1, 0, 0, 0, 1, 0, 0, 0, 1];
  const mul = (A, B) => { const C = new Array(9); for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) C[i * 3 + j] = A[i * 3] * B[j] + A[i * 3 + 1] * B[3 + j] + A[i * 3 + 2] * B[6 + j]; return C; };
  const M4 = (A) => new T.Matrix4().set(A[0], A[1], A[2], 0, A[3], A[4], A[5], 0, A[6], A[7], A[8], 0, 0, 0, 0, 1);
  const s3 = Math.sqrt(3);
  const MV = {
    A: { m: [0, 0, 1, 0, 1, 0, -1, 0, 0], ax: new T.Vector3(0, 1, 0), ang: Math.PI / 2 },           // quarter turn about the vertical (y) axis
    B: { m: [0, 0, 1, 1, 0, 0, 0, 1, 0], ax: new T.Vector3(1, 1, 1).divideScalar(s3), ang: 2 * Math.PI / 3 }, // third of a turn about (1,1,1): x -> y -> z -> x
  };

  function tex(txt, bg) {
    const c = document.createElement('canvas'); c.width = c.height = 128; const g = c.getContext('2d');
    g.fillStyle = bg; g.fillRect(0, 0, 128, 128); g.strokeStyle = 'rgba(0,0,0,0.4)'; g.lineWidth = 8; g.strokeRect(4, 4, 120, 120);
    g.fillStyle = '#fff'; g.font = '600 80px sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(txt, 64, 70);
    const t = new T.CanvasTexture(c); t.colorSpace = T.SRGBColorSpace; return t;
  }
  const cols = ['#c0504d', '#d9822b', '#c9a227', '#5f8f2f', '#3f5fa8', '#7a4fa0'];
  const mats = cols.map((c, i) => new T.MeshStandardMaterial({ map: tex(String(i + 1), c), roughness: 0.55 }));
  const geo = new T.BoxGeometry(1.7, 1.7, 1.7);
  const cube = new T.Group(); st.scene.add(cube); cube.add(new T.Mesh(geo, mats));
  cube.add(new T.LineSegments(new T.EdgesGeometry(geo), new T.LineBasicMaterial({ color: 0x222222 })));

  const lineMat = (n) => new T.Line(new T.BufferGeometry().setFromPoints(n), new T.LineBasicMaterial({ depthTest: false, transparent: true, opacity: 0.9 }));
  const vAxis = lineMat([new T.Vector3(0, -1.8, 0), new T.Vector3(0, 1.8, 0)]);
  const d = 1.7; const dAxis = lineMat([new T.Vector3(-d, -d, -d), new T.Vector3(d, d, d)]);
  vAxis.renderOrder = dAxis.renderOrder = 5; st.scene.add(vAxis, dAxis);
  const la = ctx.label('A', { size: 0.34, bold: true }); la.position.set(0, 2.1, 0); st.scene.add(la);
  const lb = ctx.label('B', { size: 0.34, bold: true }); lb.position.set(d + 0.35, d + 0.35, d + 0.35); st.scene.add(lb);

  const key = (A) => A.join(',');
  let M = I3.slice(), settled = new T.Quaternion(), queue = [], t = 0, moves = 0;
  let seen = new Map([[key(I3), 1]]);
  const cntOut = ctx.ui.readout({ label: 'Distinct orientations reached' }), barOut = ctx.ui.readout({ label: 'Out of the 24 possible' }), matOut = ctx.ui.readout({ label: 'Rotation matrix of the cube now' });
  function refresh() {
    const n = seen.size; cntOut.set(n + ' of 24' + (n === 24 ? '  (the group is complete)' : '') + ' after ' + moves + ' move' + (moves === 1 ? '' : 's'));
    barOut.set('●'.repeat(n) + '○'.repeat(24 - n));
    matOut.set('[' + [M.slice(0, 3), M.slice(3, 6), M.slice(6, 9)].map(r => r.join(' ')).join(' | ') + ']');
  }
  const qa = new T.Quaternion();
  function push(k) { queue.push(k); if (ctx.reduced) { while (queue.length) finish(); } }
  function finish() { const k = queue.shift(); M = mul(MV[k].m, M); settled.setFromRotationMatrix(M4(M)); cube.quaternion.copy(settled); t = 0; moves++; seen.set(key(M), 1); refresh(); }
  ctx.loop((dt) => {
    if (!queue.length) return;
    const k = queue[0]; t = Math.min(1, t + dt / (queue.length > 2 ? 0.22 : 0.6)); const e = t * t * (3 - 2 * t);
    qa.setFromAxisAngle(MV[k].ax, e * MV[k].ang); cube.quaternion.copy(qa).multiply(settled);
    if (t >= 1) finish();
  });
  ctx.ui.button({ label: 'A: quarter turn about vertical', onClick: () => push('A') });
  ctx.ui.button({ label: 'B: third turn about diagonal', onClick: () => push('B') });
  ctx.ui.button({ label: 'Random 12 moves', onClick: () => { for (let i = 0; i < 12; i++) push(Math.random() < 0.5 ? 'A' : 'B'); } });
  ctx.ui.button({ label: 'Reset', onClick: () => { queue = []; t = 0; M = I3.slice(); settled.identity(); cube.quaternion.identity(); moves = 0; seen = new Map([[key(I3), 1]]); refresh(); } });
  ctx.onTheme((p) => { vAxis.material.color.set(p.c1); dAxis.material.color.set(p.c3); la.userData.setColor(p.c1); lb.userData.setColor(p.c3); });
  refresh();
}
