// Differential geometry: surfaces coloured by Gaussian curvature K (analytic formulas below), plus a geodesic triangle on the unit sphere.
// Triangle: great-circle sides, angles measured between tangent vectors; area from the independent solid-angle formula of Van Oosterom and Strackee.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [3.8, 3.0, 4.6], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.8)); const sun = new T.DirectionalLight(0xffffff, 1.3); sun.position.set(3, 5, 4); st.scene.add(sun);
  const RT = 1.0, rt = 0.42; // torus radii
  // Each surface: grid size, wrap flags, position(u,v) and Gaussian curvature K(u,v), u and v in [0,1].
  const SURF = {
    sphere: { nu: 36, nv: 56, wu: false, wv: true, p: (u, v) => { const t = u * Math.PI, f = v * 2 * Math.PI; return [Math.sin(t) * Math.cos(f), Math.cos(t), Math.sin(t) * Math.sin(f)]; }, K: () => 1 },
    cylinder: { nu: 8, nv: 56, wu: false, wv: true, p: (u, v) => [Math.cos(v * 2 * Math.PI), (u - 0.5) * 2.4, Math.sin(v * 2 * Math.PI)], K: () => 0 },
    saddle: { nu: 36, nv: 36, wu: false, wv: false, p: (u, v) => { const x = (2 * u - 1) * 1.3, z = (2 * v - 1) * 1.3; return [x, (x * x - z * z) / 2, z]; },
      K: (u, v) => { const x = (2 * u - 1) * 1.3, z = (2 * v - 1) * 1.3; const w = 1 + x * x + z * z; return -1 / (w * w); } }, // z = f(x,y): K = (fxx fyy - fxy^2)/(1+|grad f|^2)^2
    torus: { nu: 56, nv: 36, wu: true, wv: true, p: (u, v) => { const f = u * 2 * Math.PI, a = v * 2 * Math.PI, r = RT + rt * Math.cos(a); return [r * Math.cos(f), rt * Math.sin(a), r * Math.sin(f)]; },
      K: (u, v) => { const c = Math.cos(v * 2 * Math.PI); return c / (rt * (RT + rt * c)); } },
  };
  const mat = new T.MeshStandardMaterial({ vertexColors: true, roughness: 0.55, metalness: 0.05, side: T.DoubleSide });
  const mesh = new T.Mesh(new T.BufferGeometry(), mat); st.scene.add(mesh);
  let Kv = null, cur = 'sphere';
  let neg = new T.Color(), pos = new T.Color(), mid = new T.Color(), tmp = new T.Color();
  function recolor() {
    if (!Kv) return; const col = mesh.geometry.attributes.color.array;
    for (let i = 0; i < Kv.length; i++) { const s = Math.sign(Kv[i]) * Math.tanh(1.3 * Math.sqrt(Math.abs(Kv[i]))), a = Math.abs(s); tmp.copy(mid).lerp(s >= 0 ? pos : neg, a); col[3 * i] = tmp.r; col[3 * i + 1] = tmp.g; col[3 * i + 2] = tmp.b; }
    mesh.geometry.attributes.color.needsUpdate = true;
  }
  const kOut = ctx.ui.readout({ label: 'Gaussian curvature K' });
  function build(name) {
    const S = SURF[name], nu = S.nu, nv = S.nv, W = S.wv ? nv : nv + 1, Hh = S.wu ? nu : nu + 1;
    const P = new Float32Array(Hh * W * 3); Kv = new Float32Array(Hh * W); let kmin = 1e9, kmax = -1e9;
    for (let i = 0; i < Hh; i++) for (let j = 0; j < W; j++) { const u = i / nu, v = j / nv, p = S.p(u, v), k = S.K(u, v), q = i * W + j; P.set(p, 3 * q); Kv[q] = k; kmin = Math.min(kmin, k); kmax = Math.max(kmax, k); }
    const idx = [], ni = S.wu ? nu : nu, nj = S.wv ? nv : nv;
    for (let i = 0; i < ni; i++) for (let j = 0; j < nj; j++) {
      const i1 = (i + 1) % Hh, j1 = (j + 1) % W, a = i * W + j, b = i * W + j1, c = i1 * W + j, d = i1 * W + j1; idx.push(a, b, c, b, d, c);
    }
    mesh.geometry.dispose(); const g = new T.BufferGeometry(); g.setAttribute('position', new T.BufferAttribute(P, 3)); g.setAttribute('color', new T.BufferAttribute(new Float32Array(Hh * W * 3), 3)); g.setIndex(idx); g.computeVertexNormals(); mesh.geometry = g;
    recolor();
    const f = (x) => (Math.abs(x) < 5e-4 ? '0' : x.toFixed(2));
    kOut.set(kmax - kmin < 1e-9 ? 'K = ' + f(kmax) + ' at every point' : 'from ' + f(kmin) + ' to ' + f(kmax) + ', changing from point to point');
  }

  // geodesic triangle on the unit sphere
  const triMat = new T.MeshBasicMaterial({ transparent: true, opacity: 0.5, side: T.DoubleSide, depthWrite: false, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2 });
  const tri = new T.Mesh(new T.BufferGeometry(), triMat); st.scene.add(tri);
  const edgeMat = new T.MeshBasicMaterial(); const edges = new T.Group(); st.scene.add(edges);
  const vm = new T.MeshBasicMaterial(); const verts = [0, 1, 2].map(() => { const m = new T.Mesh(new T.SphereGeometry(0.035, 12, 8), vm); st.scene.add(m); return m; });
  const labs = [0, 1, 2].map(() => { const l = ctx.label('90°', { size: 0.19, bold: true }); st.scene.add(l); return l; });
  const sumOut = ctx.ui.readout({ label: 'Angle sum of the triangle' }), exOut = ctx.ui.readout({ label: 'Excess over 180°' }), arOut = ctx.ui.readout({ label: 'Area on the unit sphere' });
  const c0 = new T.Vector3(1, 1, 1).normalize(), E = [new T.Vector3(1, 0, 0), new T.Vector3(0, 1, 0), new T.Vector3(0, 0, 1)];
  const DIST = { sphere: 4.3, cylinder: 4.6, saddle: 4.9, torus: 4.9 };
  let lam = 1;
  function angleAt(A, B, C) { const tb = B.clone().addScaledVector(A, -A.dot(B)).normalize(), tc = C.clone().addScaledVector(A, -A.dot(C)).normalize(); return Math.acos(Math.max(-1, Math.min(1, tb.dot(tc)))); }
  function slerp(a, b, t) { const w = Math.acos(Math.max(-1, Math.min(1, a.dot(b)))), s = Math.sin(w); return a.clone().multiplyScalar(Math.sin((1 - t) * w) / s).addScaledVector(b, Math.sin(t * w) / s); }
  function buildTri() {
    const on = cur === 'sphere'; tri.visible = edges.visible = on; verts.forEach(v => v.visible = on); labs.forEach(l => l.visible = on); slider.el.style.display = on ? '' : 'none';
    if (!on) { sumOut.el.style.display = exOut.el.style.display = arOut.el.style.display = 'none'; return; }
    sumOut.el.style.display = exOut.el.style.display = arOut.el.style.display = '';
    const V = E.map(e => c0.clone().lerp(e, lam).normalize()); const [A, B, C] = V;
    const ang = [angleAt(A, B, C), angleAt(B, C, A), angleAt(C, A, B)], sum = ang[0] + ang[1] + ang[2], deg = 180 / Math.PI;
    const area = 2 * Math.atan2(Math.abs(A.dot(B.clone().cross(C))), 1 + A.dot(B) + B.dot(C) + C.dot(A));
    sumOut.set((sum * deg).toFixed(2) + '°'); exOut.set(((sum - Math.PI) * deg).toFixed(2) + '°  =  ' + (sum - Math.PI).toFixed(4) + ' rad'); arOut.set(area.toFixed(4) + ' (equals the excess in radians)');
    // patch
    const N = 14, pts = [], ix = [], row = []; let q = 0;
    for (let i = 0; i <= N; i++) { row[i] = []; for (let j = 0; j <= N - i; j++) { const a = i / N, b = j / N, c = 1 - a - b; const p = A.clone().multiplyScalar(a).addScaledVector(B, b).addScaledVector(C, c).normalize().multiplyScalar(1.004); pts.push(p.x, p.y, p.z); row[i][j] = q++; } }
    for (let i = 0; i < N; i++) for (let j = 0; j < N - i; j++) { ix.push(row[i][j], row[i + 1][j], row[i][j + 1]); if (j < N - i - 1) ix.push(row[i + 1][j], row[i + 1][j + 1], row[i][j + 1]); }
    tri.geometry.dispose(); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(pts, 3)); g.setIndex(ix); tri.geometry = g;
    edges.children.forEach(m => { m.geometry.dispose(); }); edges.clear();
    [[A, B], [B, C], [C, A]].forEach(([a, b]) => { const cp = []; for (let k = 0; k <= 40; k++) cp.push(slerp(a, b, k / 40).multiplyScalar(1.01)); edges.add(new T.Mesh(new T.TubeGeometry(new T.CatmullRomCurve3(cp), 40, 0.014, 6), edgeMat)); });
    const m = A.clone().add(B).add(C).normalize();
    V.forEach((v, k) => { verts[k].position.copy(v).multiplyScalar(1.012); const out = v.clone().addScaledVector(m, -v.dot(m)).normalize(); labs[k].position.copy(v).multiplyScalar(1.03).addScaledVector(out, 0.2); labs[k].userData.setText(Math.round(ang[k] * deg * 10) / 10 + '°'); });
  }
  ctx.ui.select({ label: 'Surface', options: [['sphere', 'Sphere'], ['cylinder', 'Cylinder'], ['saddle', 'Saddle'], ['torus', 'Torus']], value: 'sphere', onChange: (v) => { cur = v; build(v); buildTri(); st.camera.position.setLength(DIST[v]); st.controls.update(); } });
  const slider = ctx.ui.slider({ label: 'Triangle size (sphere)', min: 0.08, max: 1, step: 0.01, value: 0.8, onInput: (v) => { lam = v; buildTri(); } });
  lam = 0.8; st.camera.position.setLength(DIST.sphere); st.controls.update();

  // legend: HTML overlay (the runtime has no 2D legend)
  const leg = document.createElement('div'); leg.style.cssText = 'position:absolute;left:10px;bottom:8px;font:600 11px/1.2 -apple-system,Segoe UI,sans-serif;pointer-events:none;width:128px';
  const bar = document.createElement('div'); bar.style.cssText = 'height:9px;border-radius:5px;margin-bottom:3px'; const row = document.createElement('div'); row.style.cssText = 'display:flex;justify-content:space-between';
  ['K < 0', 'K = 0', 'K > 0'].forEach(t => { const s = document.createElement('span'); s.textContent = t; row.append(s); });
  leg.append(bar, row); if (getComputedStyle(root).position === 'static') root.style.position = 'relative'; root.append(leg);

  ctx.onTheme((p) => {
    neg.set(p.c4); pos.set(p.c3); mid.set(p.dark ? '#8d9299' : '#d6d3c8'); recolor();
    triMat.color.set(p.c1); edgeMat.color.set(p.c1); vm.color.set(p.ink); labs.forEach(l => l.userData.setColor(p.ink));
    bar.style.background = `linear-gradient(90deg, ${p.c4}, ${mid.getStyle()}, ${p.c3})`; leg.style.color = p.ink;
  });
  build('sphere'); buildTri();
  return { dispose() { leg.remove(); } };
}
