// Convex geometry: P(s) = { |x|,|y|,|z| <= 1 } intersected with { +-x +-y +-z <= d }, d = 3 - 2s.
// s = 0: cube (d = 3 cuts nothing); s = 1/2: cuboctahedron (d = 2); s = 1: octahedron (d = 1). Vertices are found by intersecting
// triples of the 14 planes and keeping the points that satisfy every inequality; faces and edges are read off from those vertices.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [3.3, 2.6, 4.2], fov: 38 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.8)); const sun = new T.DirectionalLight(0xffffff, 1.3); sun.position.set(3, 5, 4); st.scene.add(sun);
  const EPS = 1e-7;
  const cubeN = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]];
  const octN = []; for (const a of [1, -1]) for (const b of [1, -1]) for (const c of [1, -1]) octN.push([a, b, c]);
  const det = (a, b, c) => a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0]) + a[2] * (b[0] * c[1] - b[1] * c[0]);

  function polytope(d) {
    const planes = cubeN.map(n => ({ n, d: 1, kind: 0 })).concat(octN.map(n => ({ n, d, kind: 1 })));
    const V = [];
    for (let i = 0; i < planes.length; i++) for (let j = i + 1; j < planes.length; j++) for (let k = j + 1; k < planes.length; k++) {
      const A = planes[i], B = planes[j], C = planes[k], D = det(A.n, B.n, C.n); if (Math.abs(D) < 1e-9) continue;
      const col = (m) => { // Cramer's rule: replace column m by the right-hand side
        const r = [A, B, C].map(p => { const row = p.n.slice(); row[m] = p.d; return row; }); return det(r[0], r[1], r[2]) / D;
      };
      const x = [col(0), col(1), col(2)];
      if (!planes.every(p => p.n[0] * x[0] + p.n[1] * x[1] + p.n[2] * x[2] <= p.d + EPS)) continue;
      if (!V.some(v => Math.hypot(v[0] - x[0], v[1] - x[1], v[2] - x[2]) < 1e-6)) V.push(x);
    }
    const faces = [], edgeSet = new Map();
    planes.forEach((p) => {
      const idx = []; V.forEach((v, i) => { if (Math.abs(p.n[0] * v[0] + p.n[1] * v[1] + p.n[2] * v[2] - p.d) < 1e-6) idx.push(i); });
      if (idx.length < 3) return;
      const c = [0, 0, 0]; idx.forEach(i => { for (let t = 0; t < 3; t++) c[t] += V[i][t] / idx.length; });
      const n = new T.Vector3(...p.n).normalize(), u = new T.Vector3().crossVectors(n, Math.abs(n.x) < 0.9 ? new T.Vector3(1, 0, 0) : new T.Vector3(0, 1, 0)).normalize(), w = new T.Vector3().crossVectors(n, u);
      const ang = (i) => { const q = new T.Vector3(V[i][0] - c[0], V[i][1] - c[1], V[i][2] - c[2]); return Math.atan2(q.dot(w), q.dot(u)); };
      idx.sort((a, b) => ang(a) - ang(b));
      let area = 0; for (let t = 0; t < idx.length; t++) { const a = new T.Vector3(...V[idx[t]]), b = new T.Vector3(...V[idx[(t + 1) % idx.length]]); area += a.cross(b).dot(n); }
      if (Math.abs(area) < 1e-9) return; // degenerate (collinear) contact, not a face
      faces.push({ idx, kind: p.kind, n });
      idx.forEach((a, t) => { const b = idx[(t + 1) % idx.length], key = Math.min(a, b) + '_' + Math.max(a, b); edgeSet.set(key, [a, b]); });
    });
    return { V, faces, E: [...edgeSet.values()] };
  }

  const mat = new T.MeshStandardMaterial({ vertexColors: true, roughness: 0.5, flatShading: true, side: T.DoubleSide, transparent: true, opacity: 0.92 });
  const mesh = new T.Mesh(new T.BufferGeometry(), mat); st.scene.add(mesh);
  const edgeMat = new T.LineBasicMaterial(); const edges = new T.LineSegments(new T.BufferGeometry(), edgeMat); st.scene.add(edges);
  const dualMat = new T.LineBasicMaterial({ depthTest: false, transparent: true, opacity: 0.9 }); const oc = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]], dp = [];
  for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) if (i >> 1 !== j >> 1) dp.push(...oc[i], ...oc[j]);
  const dual = new T.LineSegments(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(dp, 3)), dualMat); dual.visible = false; st.scene.add(dual);
  let col0 = new T.Color(), col1 = new T.Color(), s = 0.5;
  const vOut = ctx.ui.readout({ label: 'Vertices V' }), eOut = ctx.ui.readout({ label: 'Edges E' }), fOut = ctx.ui.readout({ label: 'Faces F' }), chiOut = ctx.ui.readout({ label: 'V − E + F' }), nameOut = ctx.ui.readout({ label: 'Shape' });
  function update() {
    const d = 3 - 2 * s, P = polytope(d), pos = [], cols = [], lp = [];
    P.faces.forEach(f => { const c = f.kind ? col1 : col0; for (let t = 1; t < f.idx.length - 1; t++) [f.idx[0], f.idx[t], f.idx[t + 1]].forEach(i => { pos.push(...P.V[i]); cols.push(c.r, c.g, c.b); }); });
    P.E.forEach(([a, b]) => lp.push(...P.V[a], ...P.V[b]));
    mesh.geometry.dispose(); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(pos, 3)); g.setAttribute('color', new T.Float32BufferAttribute(cols, 3)); g.computeVertexNormals(); mesh.geometry = g;
    edges.geometry.dispose(); edges.geometry = new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(lp, 3));
    const nV = P.V.length, nE = P.E.length, nF = P.faces.length;
    vOut.set(String(nV)); eOut.set(String(nE)); fOut.set(String(nF)); chiOut.set(nV + ' − ' + nE + ' + ' + nF + ' = ' + (nV - nE + nF));
    nameOut.set(nV === 8 && nF === 6 ? 'cube' : nV === 12 && nF === 14 ? 'cuboctahedron' : nV === 6 && nF === 8 ? 'octahedron' : s < 0.5 ? 'truncated cube (corners cut)' : 'truncated octahedron (squares and hexagons)');
    ctx.invalidate();
  }
  const slider = ctx.ui.slider({ label: 'Cut the corners: cube → octahedron', min: 0, max: 1, step: 0.01, value: s, onInput: (v) => { s = v; update(); } });
  ctx.ui.button({ label: 'Cube', onClick: () => slider.set(0) }); ctx.ui.button({ label: 'Cuboctahedron', onClick: () => slider.set(0.5) }); ctx.ui.button({ label: 'Octahedron', onClick: () => slider.set(1) });
  ctx.ui.toggle({ label: 'Show the dual octahedron', value: false, onChange: (v) => { dual.visible = v; } });
  ctx.onTheme((p) => { col0.set(p.c2); col1.set(p.c3); edgeMat.color.set(p.ink); dualMat.color.set(p.c1); update(); });
}
