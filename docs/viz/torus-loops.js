// Algebraic topology: a loop that slides on a surface. On the sphere every loop shrinks to a point; on the torus the loop
// around the tube and the loop around the hole stay circles that wind once and cannot be contracted (pi_1(torus) = Z x Z).
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [2.9, 2.5, 3.4], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.8)); const sun = new T.DirectionalLight(0xffffff, 1.3); sun.position.set(3, 5, 4); st.scene.add(sun);
  const R = 1.1, r = 0.45, TP = Math.PI * 2;
  const SF = {
    sphere: { nu: 40, nv: 56, wv: true, wu: false, p: (u, v) => { const t = u * Math.PI, f = v * TP; return [sin(t) * cos(f), cos(t), sin(t) * sin(f)]; } },
    torus: { nu: 56, nv: 32, wv: true, wu: true, p: (u, v) => { const f = u * TP, a = v * TP, q = R + r * cos(a); return [q * cos(f), r * sin(a), q * sin(f)]; } },
  };
  function sin(x) { return Math.sin(x); } function cos(x) { return Math.cos(x); }
  const surfMat = new T.MeshStandardMaterial({ transparent: true, opacity: 0.5, roughness: 0.45, side: T.DoubleSide, depthWrite: false });
  const surf = new T.Mesh(new T.BufferGeometry(), surfMat); st.scene.add(surf);
  const gridMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.28 }); const grid = new T.LineSegments(new T.BufferGeometry(), gridMat); st.scene.add(grid);
  const loopMat = new T.MeshBasicMaterial(); const loop = new T.Mesh(new T.BufferGeometry(), loopMat); st.scene.add(loop);
  const dot = new T.Mesh(new T.SphereGeometry(0.06, 16, 12), loopMat); st.scene.add(dot);
  let kind = 'sphere', which = 'tube';
  function buildSurf() {
    const S = SF[kind], nu = S.nu, nv = S.nv, W = nv, Hh = S.wu ? nu : nu + 1, pos = [], idx = [], gl = [];
    for (let i = 0; i < Hh; i++) for (let j = 0; j < W; j++) pos.push(...S.p(i / nu, j / nv));
    for (let i = 0; i < nu; i++) for (let j = 0; j < nv; j++) { const i1 = (i + 1) % Hh, j1 = (j + 1) % W, a = i * W + j, b = i * W + j1, c = i1 * W + j, d = i1 * W + j1; idx.push(a, b, c, b, d, c); }
    const nl = kind === 'sphere' ? [10, 12] : [16, 8];
    for (let a = 0; a < nl[0]; a++) for (let k = 0; k < 90; k++) gl.push(...S.p((kind === 'sphere' ? (a + 0.5) / nl[0] : a / nl[0]), k / 90), ...S.p((kind === 'sphere' ? (a + 0.5) / nl[0] : a / nl[0]), (k + 1) / 90));
    for (let b = 0; b < nl[1]; b++) for (let k = 0; k < 60; k++) gl.push(...S.p(k / 60, b / nl[1]), ...S.p((k + 1) / 60, b / nl[1]));
    surf.geometry.dispose(); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals(); surf.geometry = g;
    grid.geometry.dispose(); const gg = new T.BufferGeometry(); gg.setAttribute('position', new T.Float32BufferAttribute(gl, 3)); grid.geometry = gg;
  }
  const canOut = ctx.ui.readout({ label: 'Can this loop shrink to a point on the surface?' }), windOut = ctx.ui.readout({ label: 'What the loop goes around' }), lenOut = ctx.ui.readout({ label: 'Length of the loop' });
  let val = 0.4;
  function setLoop(pts) { // pts: closed polyline of 3D points, or null for a point
    loop.geometry.dispose(); let L = 0;
    for (let i = 0; i < pts.length; i++) L += pts[i].distanceTo(pts[(i + 1) % pts.length]);
    const tr = Math.min(0.03, 0.4 * L / TP);
    if (L / TP < 0.02) { loop.visible = false; dot.visible = true; dot.position.copy(pts[0]); lenOut.set(L.toFixed(2) + ' (a point)'); return; }
    loop.visible = true; dot.visible = false; loop.geometry = new T.TubeGeometry(new T.CatmullRomCurve3(pts, true), 120, tr, 8, true); lenOut.set(L.toFixed(2));
  }
  function update() {
    const pts = [], N = 96;
    if (kind === 'sphere') {
      const th = Math.PI / 2 * (1 - val), rho = sin(th), y = cos(th);
      for (let k = 0; k < N; k++) pts.push(new T.Vector3(rho * cos(k / N * TP), y, rho * sin(k / N * TP)));
      canOut.set(val >= 0.999 ? 'Yes: it has shrunk all the way to a point' : 'Yes: slide it up and it shrinks to the pole'); windOut.set('nothing: the sphere has no hole');
    } else if (which === 'tube') {
      const f = val * TP; for (let k = 0; k < N; k++) { const a = k / N * TP, q = R + r * cos(a); pts.push(new T.Vector3(q * cos(f), r * sin(a), q * sin(f))); }
      canOut.set('No. It slides, but stays a circle around the tube'); windOut.set('the tube, once');
    } else if (which === 'hole') {
      const a = val * TP, q = R + r * cos(a); for (let k = 0; k < N; k++) { const f = k / N * TP; pts.push(new T.Vector3(q * cos(f), r * sin(a), q * sin(f))); }
      canOut.set('No. It slides, but stays a circle around the hole'); windOut.set('the hole, once');
    } else {
      const f0 = 0.6, a0 = 0.9, rho = 0.55 * val; for (let k = 0; k < N; k++) { const al = k / N * TP, f = f0 + rho * cos(al) / (R + r * cos(a0)), a = a0 + rho * sin(al) / r, q = R + r * cos(a); pts.push(new T.Vector3(q * cos(f), r * sin(a), q * sin(f))); }
      canOut.set(val < 0.01 ? 'Yes: it has shrunk to a point' : 'Yes: it bounds a small disk on the surface, and shrinks'); windOut.set('nothing: it does not encircle the tube or the hole');
    }
    setLoop(pts); ctx.invalidate();
  }
  const DIST = { sphere: 4.3, torus: 5.3 };
  const surfSel = ctx.ui.select({ label: 'Surface', options: [['sphere', 'Sphere'], ['torus', 'Torus']], value: 'sphere', onChange: (v) => { kind = v; loopSel.el.style.display = v === 'torus' ? '' : 'none'; buildSurf(); relabel(); st.camera.position.setLength(DIST[v]); st.controls.update(); slider.set(v === 'sphere' ? 0.4 : 0.15); } });
  const loopSel = ctx.ui.select({ label: 'Loop on the torus', options: [['tube', 'Around the tube'], ['hole', 'Around the hole'], ['small', 'A small loop']], value: 'tube', onChange: (v) => { which = v; relabel(); slider.set(v === 'small' ? 0.8 : 0.15); } });
  const slider = ctx.ui.slider({ label: 'Slide the loop', min: 0, max: 1, step: 0.01, value: val, onInput: (v) => { val = v; update(); } });
  function relabel() { slider.el.querySelector('.vz-name').textContent = kind === 'sphere' ? 'Slide the loop toward the pole' : which === 'small' ? 'Size of the small loop' : 'Slide the loop around the surface'; }
  loopSel.el.style.display = 'none'; relabel(); st.camera.position.setLength(DIST.sphere); st.controls.update();
  ctx.onTheme((p) => { surfMat.color.set(p.c2); gridMat.color.set(p.ink); loopMat.color.set(p.c3); });
  buildSurf(); update();
}
