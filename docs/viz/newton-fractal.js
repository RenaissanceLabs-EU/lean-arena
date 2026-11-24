// Numerical analysis: Newton's method for p(z) = (z-a)(z-b)(z-c). Every point of the plane is colored by the root its iteration reaches.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 4.4, pos: [0, 0, 10] });
  const S3 = Math.sqrt(3) / 2;
  const presets = {
    cube: ['Cube roots of unity', [[1, 0], [-0.5, S3], [-0.5, -S3]]],
    squash: ['A squashed triangle', [[-1.4, -0.25], [1.4, -0.25], [0, 0.45]]],
    flat: ['Almost in a line', [[-1.5, 0], [0, 0.18], [1.5, 0]]],
  };
  const roots = presets.cube[1].map(r => new T.Vector2(r[0], r[1]));
  const uni = {
    uA: { value: roots[0] }, uB: { value: roots[1] }, uC: { value: roots[2] }, uIter: { value: 12 },
    k0: { value: new T.Color() }, k1: { value: new T.Color() }, k2: { value: new T.Color() }, bg: { value: new T.Color() },
  };
  const mat = new T.ShaderMaterial({
    uniforms: uni,
    vertexShader: 'varying vec2 vP; void main(){ vP = position.xy; gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0); }',
    fragmentShader: `
      varying vec2 vP; uniform vec2 uA, uB, uC; uniform float uIter; uniform vec3 k0, k1, k2, bg;
      vec2 cmul(vec2 a, vec2 b){ return vec2(a.x*b.x - a.y*b.y, a.x*b.y + a.y*b.x); }
      vec2 cdiv(vec2 a, vec2 b){ return vec2(a.x*b.x + a.y*b.y, a.y*b.x - a.x*b.y) / dot(b, b); }
      void main(){
        vec2 z = vP; vec3 col = bg; bool conv = false;
        for (int i = 0; i < 31; i++) {
          vec2 za = z - uA, zb = z - uB, zc = z - uC;
          float d0 = dot(za, za), d1 = dot(zb, zb), d2 = dot(zc, zc);
          float dm = min(d0, min(d1, d2));
          if (dm < 1e-6) { // within 0.001 of a root: converged after i steps
            vec3 base = d0 == dm ? k0 : (d1 == dm ? k1 : k2);
            col = base * (0.3 + 0.7 * exp(-float(i) * 0.13)); conv = true; break;
          }
          if (float(i) >= uIter) break;
          vec2 p = cmul(cmul(za, zb), zc);
          vec2 dp = cmul(zb, zc) + cmul(za, zc) + cmul(za, zb);
          if (dot(dp, dp) < 1e-12) break; // p'(z) = 0: Newton step undefined
          z -= cdiv(p, dp);
          if (!(abs(z.x) < 1e6 && abs(z.y) < 1e6)) break;
        }
        if (!conv) { // not settled yet: a faint tint of the nearest root
          float e0 = dot(z - uA, z - uA), e1 = dot(z - uB, z - uB), e2 = dot(z - uC, z - uC), em = min(e0, min(e1, e2));
          col = mix(bg, e0 == em ? k0 : (e1 == em ? k1 : k2), 0.22);
        }
        gl_FragColor = vec4(col, 1.0);
        #include <colorspace_fragment>
      }`,
  });
  const plane = new T.Mesh(new T.PlaneGeometry(60, 60), mat); plane.frustumCulled = false; st.scene.add(plane);

  const disc = new T.CircleGeometry(1, 24);
  const outer = roots.map(() => { const m = new T.Mesh(disc, new T.MeshBasicMaterial()); m.scale.set(0.15, 0.15, 1); m.position.z = 1; st.scene.add(m); return m; });
  const inner = roots.map(() => { const m = new T.Mesh(disc, new T.MeshBasicMaterial()); m.scale.set(0.1, 0.1, 1); m.position.z = 1.1; st.scene.add(m); return m; });
  function place() { roots.forEach((r, i) => { outer[i].position.x = inner[i].position.x = r.x; outer[i].position.y = inner[i].position.y = r.y; }); ctx.invalidate(); }

  const sel = ctx.ui.select({
    label: 'Roots', options: Object.entries(presets).map(([k, v]) => [k, v[0]]).concat([['custom', 'Custom (dragged)']]), value: 'cube',
    onChange: (k) => { if (!presets[k]) return; presets[k][1].forEach((r, i) => roots[i].set(r[0], r[1])); place(); upd(); },
  });
  ctx.ui.slider({ label: 'Iterations shown', min: 1, max: 30, step: 1, value: uni.uIter.value, onInput: (v) => { uni.uIter.value = v; } });
  const out = ctx.ui.readout({ label: 'Roots' });
  const fmt = (r) => r.x.toFixed(2) + (r.y < 0 ? ' − ' : ' + ') + Math.abs(r.y).toFixed(2) + 'i';
  const upd = () => out.set(roots.map(fmt).join(',  '));

  let grab = -1;
  ctx.pointer(st.renderer.domElement, {
    down: (p) => {
      const wx = p.x * st.camera.right, wy = p.y * st.camera.top; let bd = 0.6; grab = -1;
      roots.forEach((r, i) => { const d = Math.hypot(r.x - wx, r.y - wy); if (d < bd) { bd = d; grab = i; } });
    },
    move: (p, down) => {
      if (!down || grab < 0) return;
      roots[grab].set(Math.max(-st.camera.right + 0.1, Math.min(st.camera.right - 0.1, p.x * st.camera.right)), Math.max(-st.camera.top + 0.1, Math.min(st.camera.top - 0.1, p.y * st.camera.top)));
      sel.el.querySelector('select').value = 'custom'; place(); upd();
    },
  });

  ctx.onTheme((p) => {
    uni.k0.value.set(p.c2); uni.k1.value.set(p.c3); uni.k2.value.set(p.c1); uni.bg.value.set(p.dark ? '#26231d' : '#efe9dc');
    outer.forEach(m => m.material.color.set(p.ink)); inner.forEach((m, i) => m.material.color.set(p.paper));
  });
  place(); upd();
}
