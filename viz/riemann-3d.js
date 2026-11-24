// Measure and integration: the volume under z = f(x, y) on [-1, 1]^2 as a sum of columns.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [2.7, 2.3, 3.3], target: [0, 0.55, 0], fov: 38 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.75)); const sun = new T.DirectionalLight(0xffffff, 1.3); sun.position.set(2, 5, 3); st.scene.add(sun);
  const funcs = {
    hill: { name: 'Hill', f: (x, y) => 0.15 + 1.6 * Math.exp(-2.5 * (x * x + y * y)) },
    waves: { name: 'Waves', f: (x, y) => 0.9 + 0.55 * Math.sin(2.4 * x) * Math.cos(2.6 * y) + 0.2 * x },
    bowl: { name: 'Bowl', f: (x, y) => 0.2 + 0.75 * (x * x + y * y) },
    ripple: { name: 'Ripple', f: (x, y) => 0.9 + 0.7 * Math.cos(4.5 * Math.hypot(x, y)) * Math.exp(-(x * x + y * y)) },
  };
  let key = 'hill', n = 8, mid = false;
  const refCache = {};
  function reference(k) { // midpoint rule on a 500 x 500 grid: error far below anything visible at n <= 40
    if (refCache[k] != null) return refCache[k];
    const M = 500, h = 2 / M, f = funcs[k].f; let s = 0;
    for (let i = 0; i < M; i++) for (let j = 0; j < M; j++) s += f(-1 + (i + 0.5) * h, -1 + (j + 0.5) * h);
    return (refCache[k] = s * h * h);
  }

  const NMAX = 40;
  const colMat = new T.MeshStandardMaterial({ roughness: 0.55, metalness: 0.05, transparent: true, opacity: 0.5, side: T.DoubleSide, depthWrite: false });
  const cols = new T.InstancedMesh(new T.BoxGeometry(1, 1, 1), colMat, NMAX * NMAX); cols.frustumCulled = false; cols.renderOrder = 2; st.scene.add(cols);
  const S = 56, sg = new T.PlaneGeometry(2, 2, S, S); sg.rotateX(-Math.PI / 2);
  const surfMat = new T.MeshStandardMaterial({ roughness: 0.4, transparent: true, opacity: 0.9, side: T.DoubleSide });
  const surf = new T.Mesh(sg, surfMat); st.scene.add(surf);
  const sp = sg.attributes.position;
  function shape() { for (let i = 0; i < sp.count; i++) sp.setY(i, funcs[key].f(sp.getX(i), sp.getZ(i))); sp.needsUpdate = true; sg.computeVertexNormals(); }
  const grid = new T.GridHelper(2, 8); grid.material.transparent = true; grid.material.opacity = 0.7; st.scene.add(grid);
  const frame = new T.LineSegments(new T.EdgesGeometry(new T.BoxGeometry(2, 0.0001, 2)), new T.LineBasicMaterial()); st.scene.add(frame);

  const sumOut = ctx.ui.readout({ label: 'Riemann sum' }), refOut = ctx.ui.readout({ label: 'Reference (500 x 500 grid)' });
  const errOut = ctx.ui.readout({ label: 'Error (sum − reference)' }), scaleOut = ctx.ui.readout({ label: 'Error × n' });
  const m4 = new T.Matrix4(), q = new T.Quaternion(), pv = new T.Vector3(), sv = new T.Vector3();
  function update() {
    const f = funcs[key].f, c = 2 / n; let s = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const x0 = -1 + i * c, y0 = -1 + j * c, off = mid ? c / 2 : 0; const h = f(x0 + off, y0 + off); s += h;
      pv.set(x0 + c / 2, h / 2, y0 + c / 2); sv.set(c * 0.94, Math.max(Math.abs(h), 1e-4), c * 0.94);
      m4.compose(pv, q, sv); cols.setMatrixAt(i * n + j, m4);
    }
    cols.count = n * n; cols.instanceMatrix.needsUpdate = true;
    s *= c * c; const R = reference(key), e = s - R;
    sumOut.set(s.toFixed(5)); refOut.set(R.toFixed(5));
    errOut.set((e >= 0 ? '+' : '−') + Math.abs(e).toExponential(2) + '  (' + (100 * Math.abs(e) / R).toFixed(2) + '% of the volume)');
    scaleOut.el.querySelector('.vz-name').textContent = mid ? 'Error × n²' : 'Error × n';
    scaleOut.set((e * (mid ? n * n : n)).toFixed(4));
    ctx.invalidate();
  }
  ctx.ui.select({ label: 'Surface z = f(x, y)', options: Object.entries(funcs).map(([k, v]) => [k, v.name]), value: key, onChange: (k) => { key = k; shape(); update(); } });
  ctx.ui.slider({ label: 'Grid size n (n × n columns)', min: 1, max: NMAX, step: 1, value: n, onInput: (v) => { n = v; update(); } });
  ctx.ui.toggle({ label: 'Midpoint rule (default: left corner)', value: mid, onChange: (v) => { mid = v; update(); } });
  ctx.onTheme((p) => { colMat.color.set(p.c2); surfMat.color.set(p.c1); grid.material.color.set(p.rule); frame.material.color.set(p.ink); });
  shape(); update();
}
