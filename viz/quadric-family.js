// Algebraic geometry: the level sets x^2 + y^2 - z^2 = t. Symmetry axis (z) is drawn vertical.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [4.6, 3.0, 5.6], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.75)); const sun = new T.DirectionalLight(0xffffff, 1.3); sun.position.set(3, 5, 4); st.scene.add(sun);
  const H = 1.5, NT = 56;
  const surfMat = new T.MeshStandardMaterial({ transparent: true, opacity: 0.55, roughness: 0.4, side: T.DoubleSide, depthWrite: false });
  const surf = new T.Mesh(new T.BufferGeometry(), surfMat); st.scene.add(surf);
  const wireMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.35 });
  const wire = new T.LineSegments(new T.BufferGeometry(), wireMat); st.scene.add(wire);
  const NR = 18; // lines per family
  const mkLines = () => { const g = new T.BufferGeometry(); g.setAttribute('position', new T.BufferAttribute(new Float32Array(NR * 6), 3)); return g; };
  const ruleA = new T.LineSegments(mkLines(), new T.LineBasicMaterial()); const ruleB = new T.LineSegments(mkLines(), new T.LineBasicMaterial());
  st.scene.add(ruleA, ruleB);
  const axis = new T.Line(new T.BufferGeometry().setFromPoints([new T.Vector3(0, -H - 0.3, 0), new T.Vector3(0, H + 0.3, 0)]), new T.LineBasicMaterial({ transparent: true, opacity: 0.6 }));
  st.scene.add(axis);
  const dot = new T.Mesh(new T.SphereGeometry(0.07, 20, 14), new T.MeshBasicMaterial()); st.scene.add(dot);
  const zl = ctx.label('z', { size: 0.28 }); zl.position.set(0, H + 0.5, 0); st.scene.add(zl);
  let tval = 0.6, rules = true, play = false, dir = 1;

  // scene coordinates: (x, y, z) -> (x, z, y) so z is up
  const P = (out, i, x, y, z) => { out[i] = x; out[i + 1] = z; out[i + 2] = y; };

  function build() {
    const pos = [], idx = [], wl = [];
    const eps = 0.004, a = Math.sqrt(Math.abs(tval));
    const grids = []; // each: function (i in 0..1, th) -> [x,y,z]
    if (Math.abs(tval) < eps) {
      grids.push((u, th) => { const h = u * H; return [h * Math.cos(th), h * Math.sin(th), h]; });
      grids.push((u, th) => { const h = -u * H; return [-h * Math.cos(th), -h * Math.sin(th), h]; });
    } else if (tval > 0) {
      const sm = Math.asinh(H / a);
      grids.push((u, th) => { const s = (2 * u - 1) * sm, r = a * Math.cosh(s); return [r * Math.cos(th), r * Math.sin(th), a * Math.sinh(s)]; });
    } else {
      const sm = Math.acosh(H / a);
      grids.push((u, th) => { const s = u * sm; return [a * Math.sinh(s) * Math.cos(th), a * Math.sinh(s) * Math.sin(th), a * Math.cosh(s)]; });
      grids.push((u, th) => { const s = u * sm; return [a * Math.sinh(s) * Math.cos(th), a * Math.sinh(s) * Math.sin(th), -a * Math.cosh(s)]; });
    }
    const NU = 24;
    grids.forEach((f) => {
      const base = pos.length / 3;
      for (let i = 0; i <= NU; i++) for (let j = 0; j <= NT; j++) { const p = f(i / NU, j / NT * Math.PI * 2); pos.push(p[0], p[2], p[1]); }
      for (let i = 0; i < NU; i++) for (let j = 0; j < NT; j++) { const q = base + i * (NT + 1) + j; idx.push(q, q + 1, q + NT + 1, q + 1, q + NT + 2, q + NT + 1); }
      // parallel circles as faint wire
      for (let i = 0; i <= NU; i += 4) for (let j = 0; j < NT; j++) { const p = f(i / NU, j / NT * Math.PI * 2), q = f(i / NU, (j + 1) / NT * Math.PI * 2); wl.push(p[0], p[2], p[1], q[0], q[2], q[1]); }
    });
    surf.geometry.dispose(); const g = new T.BufferGeometry();
    g.setAttribute('position', new T.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals(); surf.geometry = g;
    wire.geometry.dispose(); const wg = new T.BufferGeometry(); wg.setAttribute('position', new T.Float32BufferAttribute(wl, 3)); wire.geometry = wg;

    // rulings: lines (a cos p - s sin p, a sin p + s cos p, +-s) lie on the surface when t >= 0 (a = sqrt t; a = 0 is the cone)
    const ok = tval > -eps && rules;
    ruleA.visible = ruleB.visible = ok;
    if (ok) {
      const A = ruleA.geometry.attributes.position.array, B = ruleB.geometry.attributes.position.array;
      for (let k = 0; k < NR; k++) {
        const p = k / NR * Math.PI * 2, c = Math.cos(p), s = Math.sin(p), r0 = Math.abs(tval) < eps ? 0 : a;
        // keep the line inside the height window: z = +-S
        P(A, k * 6, r0 * c + H * s, r0 * s - H * c, -H); P(A, k * 6 + 3, r0 * c - H * s, r0 * s + H * c, H);
        P(B, k * 6, r0 * c + H * s, r0 * s - H * c, H); P(B, k * 6 + 3, r0 * c - H * s, r0 * s + H * c, -H);
      }
      ruleA.geometry.attributes.position.needsUpdate = true; ruleB.geometry.attributes.position.needsUpdate = true;
    }
    dot.visible = Math.abs(tval) < eps;
    const p = ctx.palette();
    surfMat.color.set(tval < -eps ? p.c4 : tval > eps ? p.c2 : p.c3);
    const kind = tval < -eps ? 'two-sheeted hyperboloid, smooth' : tval > eps ? 'one-sheeted hyperboloid, smooth' : 'double cone, singular at the origin';
    const isTwo = tval < -eps;
    typeOut.set(kind); linesOut.set(isTwo ? 'none: the two sheets contain no straight lines' : (tval > eps ? 'two families through every point' : 'lines through the origin'));
    grad.set(Math.abs(tval) < eps ? 'zero at the origin, which lies on the surface' : 'nonzero at every point of the surface');
    ctx.invalidate();
  }
  const typeOut = ctx.ui.readout({ label: 'Surface' }), linesOut = ctx.ui.readout({ label: 'Straight lines on it' }), grad = ctx.ui.readout({ label: 'Gradient (2x, 2y, −2z)' });
  const slider = ctx.ui.slider({ label: 't in x² + y² − z² = t', min: -1.5, max: 1.5, step: 0.05, value: tval, format: (v) => (Math.abs(v) < 1e-9 ? '0.00' : (v > 0 ? '+' : '−') + Math.abs(v).toFixed(2)), onInput: (v) => { tval = Math.abs(v) < 1e-9 ? 0 : v; build(); } });
  ctx.ui.toggle({ label: 'Show straight lines', value: true, onChange: (v) => { rules = v; build(); } });
  ctx.ui.button({ label: 'Sweep t', onClick: () => { sv = slider.get(); play = true; } });
  let sv = 0;
  ctx.loop((dt) => {
    if (!play) return; sv += dir * dt * 0.7;
    if (sv >= 1.5) { sv = 1.5; dir = -1; } if (sv <= -1.5) { sv = -1.5; dir = 1; play = false; }
    slider.set(Math.round(sv * 20) / 20);
  });
  ctx.onTheme((p) => {
    wireMat.color.set(p.ink); ruleA.material.color.set(p.c1); ruleB.material.color.set(p.c5); axis.material.color.set(p.inkSoft); dot.material.color.set(p.c1);
    zl.userData.setColor(p.inkSoft); surfMat.color.set(tval < -1e-3 ? p.c4 : tval > 1e-3 ? p.c2 : p.c3);
  });
  build();
}
