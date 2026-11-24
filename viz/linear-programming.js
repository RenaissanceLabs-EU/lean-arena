// Operations research: a linear objective over a polytope is always optimized at a corner. Vertices come from intersecting
// triples of constraint planes and keeping the feasible ones; the optimum is the vertex with the largest c . v.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [9.4, 6.6, 5.6], target: [1.4, 1.3, -1.5], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 1.5)); const sun = new T.DirectionalLight(0xffffff, 0.8); sun.position.set(4, 7, 5); st.scene.add(sun);
  // a x <= b, with x, y, z >= 0 written as -x <= 0 etc.
  const CONS = [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [1, 1, 0, 4], [0, 1, 1, 4.5], [1, 0, 1, 4], [1, 1, 1, 5.5], [1, 0, 0, 3], [0, 0, 1, 3.2]];
  const EPS = 1e-9, W = (v) => [v[0], v[2], -v[1]]; // problem (x, y, z) -> scene (x, z, -y): z is up, the map keeps orientation
  const det3 = (a, b, c) => a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]);
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
  const norm = (a) => { const l = Math.hypot(...a) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };

  // vertices by Cramer's rule on every triple of planes
  const verts = [];
  for (let i = 0; i < CONS.length; i++) for (let j = i + 1; j < CONS.length; j++) for (let k = j + 1; k < CONS.length; k++) {
    const a = CONS[i], b = CONS[j], c = CONS[k], D = det3(a, b, c); if (Math.abs(D) < 1e-9) continue;
    const bb = [a[3], b[3], c[3]], M = [a, b, c].map(r => r.slice(0, 3));
    const rep = (idx) => M.map((r, m) => r.map((x, q) => (q === idx ? bb[m] : x)));
    const v = [det3(...rep(0)) / D, det3(...rep(1)) / D, det3(...rep(2)) / D];
    if (!CONS.every(r => dot(r, v) <= r[3] + 1e-7)) continue;
    if (!verts.some(u => Math.hypot(u[0] - v[0], u[1] - v[1], u[2] - v[2]) < 1e-6)) verts.push(v);
  }
  // faces: for each constraint, the vertices on its plane, ordered around their centroid
  const faces = [];
  for (const r of CONS) {
    const on = verts.filter(v => Math.abs(dot(r, v) - r[3]) < 1e-6); if (on.length < 3) continue;
    const cen = on.reduce((s, v) => [s[0] + v[0] / on.length, s[1] + v[1] / on.length, s[2] + v[2] / on.length], [0, 0, 0]);
    const nn = norm(r), e1 = norm(sub(on[0], cen)), e2 = cross(nn, e1);
    on.sort((p, q) => Math.atan2(dot(sub(p, cen), e2), dot(sub(p, cen), e1)) - Math.atan2(dot(sub(q, cen), e2), dot(sub(q, cen), e1)));
    faces.push(on);
  }
  const tri = [], edge = [];
  for (const f of faces) {
    const p0 = W(f[0]); for (let i = 1; i < f.length - 1; i++) tri.push(...p0, ...W(f[i]), ...W(f[i + 1]));
    for (let i = 0; i < f.length; i++) edge.push(...W(f[i]), ...W(f[(i + 1) % f.length]));
  }
  const geo = new T.BufferGeometry(); geo.setAttribute('position', new T.Float32BufferAttribute(tri, 3)); geo.computeVertexNormals();
  const bodyMat = new T.MeshStandardMaterial({ transparent: true, opacity: 0.5, side: T.DoubleSide, depthWrite: false, roughness: 0.6, metalness: 0 });
  st.scene.add(new T.Mesh(geo, bodyMat));
  const eGeo = new T.BufferGeometry(); eGeo.setAttribute('position', new T.Float32BufferAttribute(edge, 3));
  const edgeMat = new T.LineBasicMaterial(); st.scene.add(new T.LineSegments(eGeo, edgeMat));
  const dotGeo = new T.SphereGeometry(0.07, 12, 8), dots = verts.map((v) => { const m = new T.Mesh(dotGeo, new T.MeshBasicMaterial()); st.scene.add(m); m.position.set(...W(v)); return m; });

  const grid = new T.GridHelper(8, 8); grid.position.set(2, 0, -2); st.scene.add(grid);
  const axG = new T.BufferGeometry().setFromPoints([[0, 0, 0], [4.4, 0, 0], [0, 0, 0], [0, 3.8, 0], [0, 0, 0], [0, 0, -4.6]].map(p => new T.Vector3(...p))); // scene axes: x, z (up), -y
  const axes = new T.LineSegments(axG, new T.LineBasicMaterial()); st.scene.add(axes);
  [['x', [4.7, 0, 0]], ['z', [0, 4.1, 0]], ['y', [0, 0, -4.9]]].forEach(([t, p]) => { const l = ctx.label(t, { size: 0.36 }); l.position.set(...p); st.scene.add(l); l.userData.t = t; axes.userData[t] = l; });

  const plane = new T.Mesh(new T.PlaneGeometry(5.5, 5.5), new T.MeshBasicMaterial({ transparent: true, opacity: 0.22, side: T.DoubleSide, depthWrite: false })); st.scene.add(plane);
  const arrow = new T.ArrowHelper(new T.Vector3(0, 1, 0), new T.Vector3(), 1.5, 0xffffff, 0.3, 0.18); st.scene.add(arrow);
  const outC = ctx.ui.readout({ label: 'Objective direction c' }), outV = ctx.ui.readout({ label: 'Largest value of c · x' }), outX = ctx.ui.readout({ label: 'Optimal vertex (x, y, z)' });

  let az = 40, el = 35, push = 1;
  function update() {
    const a = az * Math.PI / 180, b = el * Math.PI / 180, c = [Math.cos(b) * Math.cos(a), Math.cos(b) * Math.sin(a), Math.sin(b)];
    let best = -Infinity; for (const v of verts) best = Math.max(best, dot(c, v));
    const ties = verts.map((v, i) => i).filter(i => dot(c, verts[i]) > best - 1e-9);
    let low = Infinity; for (const v of verts) low = Math.min(low, dot(c, v));
    verts.forEach((v, i) => { const opt = ties.includes(i); dots[i].scale.setScalar(opt ? 2.6 : 1); dots[i].material.color.set(opt ? col.gold : col.ink); dots[i].material.depthTest = !opt; dots[i].renderOrder = opt ? 5 : 0; });
    const level = (low - 0.6) + push * (best - (low - 0.6)); // the plane c . x = level; push = 1 touches the polytope at the optimum
    const cw = new T.Vector3(...W(c));
    plane.position.copy(cw.clone().multiplyScalar(level)); plane.quaternion.setFromUnitVectors(new T.Vector3(0, 0, 1), cw);
    const ax = ties.reduce((s, i) => [s[0] + verts[i][0] / ties.length, s[1] + verts[i][1] / ties.length, s[2] + verts[i][2] / ties.length], [0, 0, 0]);
    arrow.position.set(...W(ax)); arrow.setDirection(cw);
    const f = (x) => x.toFixed(2);
    outC.set('(' + c.map(f).join(', ') + ')'); outV.set(best.toFixed(3) + (push < 1 ? '   (plane at ' + level.toFixed(2) + ')' : ''));
    outX.set(ties.length === 1 ? '(' + verts[ties[0]].map(f).join(', ') + ')' : 'tie between ' + ties.length + ' corners, e.g. (' + verts[ties[0]].map(f).join(', ') + ')');
    ctx.invalidate();
  }
  ctx.ui.slider({ label: 'Direction around (degrees)', min: 0, max: 360, step: 1, value: az, onInput: (v) => { az = v; update(); } });
  ctx.ui.slider({ label: 'Direction upward (degrees)', min: -90, max: 90, step: 1, value: el, onInput: (v) => { el = v; update(); } });
  ctx.ui.slider({ label: 'Push the plane (0 to 1)', min: 0, max: 1, step: 0.01, value: push, onInput: (v) => { push = v; update(); } });

  const col = { gold: '#000', ink: '#000' };
  ctx.onTheme((p) => {
    col.gold = p.c1; col.ink = p.inkSoft; bodyMat.color.set(p.c2); edgeMat.color.set(p.ink); plane.material.color.set(p.c3); arrow.setColor(p.c3);
    grid.material.color.set(p.rule); grid.material.transparent = true; grid.material.opacity = 0.5; axes.material.color.set(p.inkSoft);
    ['x', 'y', 'z'].forEach(t => axes.userData[t].userData.setColor(p.inkSoft)); update();
  });
}
