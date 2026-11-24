// Order theory: the divisors of n ordered by divisibility form a lattice (a Hasse diagram).
// Click a divisor to light its down-set (divisors of it) and up-set (its multiples that divide n).
// The last two clicks a, b give gcd = meet and lcm = join; both are checked against the order itself.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ pos: [5.4, 1.2, 4.8], fov: 40 });
  st.scene.add(new T.AmbientLight(0xffffff, 0.85)); const sun = new T.DirectionalLight(0xffffff, 1.2); sun.position.set(3, 5, 4); st.scene.add(sun);
  const grp = new T.Group(); st.scene.add(grp);
  const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
  const lcm = (a, b) => a / gcd(a, b) * b;
  let pal = ctx.palette();

  let n = 30, primes = [], divs = [], exps = [], pos = [], spheres = [], edges = [], halos = [];
  let sel = [], vtxMat = [], clear = [];
  const sphG = new T.SphereGeometry(0.24, 24, 16), cylG = new T.CylinderGeometry(1, 1, 1, 8, 1, true), haloG = new T.SphereGeometry(0.38, 20, 12);
  const out = ctx.ui.readout({ label: 'Last two clicked' }), gOut = ctx.ui.readout({ label: 'gcd (meet)' }), lOut = ctx.ui.readout({ label: 'lcm (join)' });

  function factor(m) { const ps = []; for (let p = 2; m > 1; p++) if (m % p === 0) { let e = 0; while (m % p === 0) { m /= p; e++; } ps.push([p, e]); } return ps; }
  function layout(e, k, fac) { // exponent vector -> 3D position
    if (k <= 3) return [e[0] * 1.2 - 0.6 * fac[0][1], (e[1] || 0) * 1.2 - 0.6 * ((fac[1] || [0, 0])[1]), (e[2] || 0) * 1.2 - 0.6 * ((fac[2] || [0, 0])[1])];
    return null;
  }
  function build() {
    grp.children.slice().forEach((o) => { grp.remove(o); if (o.userData.setText) o.material.map.dispose(); });
    const fac = factor(n); primes = fac.map((f) => f[0]); const k = fac.length;
    divs = []; exps = [];
    const rec = (i, d, e) => { if (i === k) { divs.push(d); exps.push(e.slice()); return; } for (let j = 0; j <= fac[i][1]; j++) { e[i] = j; rec(i + 1, d * Math.pow(fac[i][0], j), e); } };
    rec(0, 1, []);
    const order = divs.map((_, i) => i).sort((a, b) => divs[a] - divs[b]); divs = order.map((i) => divs[i]); exps = order.map((i) => exps[i]);
    // positions
    const up = new T.Quaternion().setFromUnitVectors(new T.Vector3(1, 1, 1).normalize(), new T.Vector3(0, 1, 0));
    const ang = [0, 70, 150, 250].map((a) => a * Math.PI / 180);
    pos = exps.map((e) => {
      if (k === 2) { const s = 0.85; return [(e[0] - e[1]) * s, (e[0] + e[1] - (fac[0][1] + fac[1][1]) / 2) * s * 1.1, 0]; }
      if (k === 4) { let x = 0, z = 0, r = 0; e.forEach((v, i) => { x += v * Math.cos(ang[i]); z += v * Math.sin(ang[i]); r += v; }); return [x, r, z]; }
      const v = new T.Vector3(e[0], e[1], e[2] || 0).applyQuaternion(up); return [v.x, v.y, v.z]; // a true cube / box, stood on its corner so height = rank
    });
    const c = [0, 1, 2].map((a) => (Math.min(...pos.map((p) => p[a])) + Math.max(...pos.map((p) => p[a]))) / 2);
    pos = pos.map((p) => new T.Vector3(p[0] - c[0], p[1] - c[1], p[2] - c[2]));
    const ext = Math.max(...pos.map((p) => p.length())); const sc = (k === 4 ? 1.8 : 1.75) / ext; pos.forEach((p) => p.multiplyScalar(sc)); grp.scale.setScalar(1);
    spheres = []; vtxMat = []; halos = []; edges = [];
    divs.forEach((d, i) => {
      const mat = new T.MeshStandardMaterial({ roughness: 0.4 }); const s = new T.Mesh(sphG, mat); s.position.copy(pos[i]); s.userData.i = i; grp.add(s); spheres.push(s); vtxMat.push(mat);
      const hm = new T.MeshBasicMaterial({ wireframe: true, transparent: true, opacity: 0.8 }); const h = new T.Mesh(haloG, hm); h.position.copy(pos[i]); h.visible = false; grp.add(h); halos.push(h);
      const lb = ctx.label(String(d), { size: k === 4 ? 0.22 : 0.27, bold: true }); lb.userData.i = i; lb.position.copy(pos[i]).add(new T.Vector3(0, 0.5, 0)); grp.add(lb);
    });
    divs.forEach((d, i) => primes.forEach((p, pi) => { const j = divs.indexOf(d * p); if (j < 0) return;
      const m = new T.MeshBasicMaterial({ transparent: true }); const cy = new T.Mesh(cylG, m); const a = pos[i], b = pos[j];
      cy.position.copy(a).add(b).multiplyScalar(0.5); cy.quaternion.setFromUnitVectors(new T.Vector3(0, 1, 0), b.clone().sub(a).normalize());
      cy.userData = { len: a.distanceTo(b), i, j }; cy.scale.set(0.025, cy.userData.len, 0.025); grp.add(cy); edges.push(cy);
      if (i === 0) { const t = ctx.label('×' + p, { size: 0.26 }); t.position.copy(a).add(b).multiplyScalar(0.5).add(new T.Vector3(0.0, -0.05, 0.28)); grp.add(t); t.userData.edgeLabel = true; }
    }));
    // defaults: two divisors with a visible gcd and lcm
    const idx = (e) => exps.findIndex((x) => x.every((v, q) => v === e[q]));
    const e1 = fac.map((f, q) => (k >= 3 ? (q < 2 ? 1 : 0) : (q === 0 ? Math.min(2, f[1]) : 1)));
    const e2 = fac.map((f, q) => (k >= 3 ? (q === 0 || q === 2 ? 1 : 0) : (q === 0 ? 1 : Math.min(2, f[1]))));
    sel = [idx(e1), idx(e2)].filter((v) => v >= 0); if (sel.length < 2) sel = [1, Math.min(2, divs.length - 1)];
    restyle();
  }
  const leq = (a, b) => b % a === 0; // a divides b
  function restyle() {
    const [pa, pb] = [divs[sel[0]], divs[sel[1]]]; const last = pb;
    const g = gcd(pa, pb), l = lcm(pa, pb);
    // meet and join found from the order alone: greatest common lower bound, least common upper bound
    const lower = divs.filter((d) => leq(d, pa) && leq(d, pb)), upper = divs.filter((d) => leq(pa, d) && leq(pb, d));
    const meet = lower.find((d) => lower.every((x) => leq(x, d))), join = upper.find((d) => upper.every((x) => leq(d, x)));
    const ok = meet === g && join === l;
    out.set(pa + ', ' + pb); gOut.set(g + (ok ? '  = greatest common divisor in the order' : '  (check failed)')); lOut.set(l + (ok ? '  = least common multiple in the order' : ''));
    vtxMat.forEach((m, i) => {
      const d = divs[i]; let col = pal.dark ? '#5a5f68' : '#b9b3a6', sc = 1;
      if (leq(d, last)) col = pal.c2; if (leq(last, d)) col = pal.c1; if (d === last) { col = pal.c3; sc = 1.35; } else if (d === (sel[0] === sel[1] ? -1 : pa)) { col = pal.c4; sc = 1.2; }
      m.color.set(col); spheres[i].scale.setScalar(sc); halos[i].visible = d === g || d === l; halos[i].material.color.set(pal.ink);
    });
    edges.forEach((e) => {
      const a = divs[e.userData.i], b = divs[e.userData.j]; let col = pal.dark ? '#5a5f68' : '#b9b3a6', w = 0.025;
      if (leq(b, last)) { col = pal.c2; w = 0.05; } else if (leq(last, a)) { col = pal.c1; w = 0.05; }
      e.material.color.set(col); e.scale.set(w, e.userData.len, w);
    });
    ctx.invalidate();
  }
  ctx.onTheme((p) => { pal = p; grp.children.forEach((o) => { if (o.userData.setColor) o.userData.setColor(p.ink); }); if (divs.length) restyle(); });

  ctx.ui.select({ label: 'n', options: [['30', '30 = 2·3·5'], ['60', '60 = 2²·3·5'], ['36', '36 = 2²·3²'], ['210', '210 = 2·3·5·7']], value: '30', onChange: (v) => { n = +v; build(); relabel(); } });
  function relabel() { grp.children.forEach((o) => { if (o.userData.setColor) o.userData.setColor(pal.ink); }); }
  ctx.ui.button({ label: 'Reset view', onClick: () => { st.camera.position.set(5.4, 1.2, 4.8); st.controls.update(); } });

  // click (not drag) picks a divisor with a raycaster
  const ray = new T.Raycaster(), v2 = new T.Vector2(); let down = null; const dom = st.renderer.domElement;
  dom.addEventListener('pointerdown', (e) => { down = [e.clientX, e.clientY]; });
  dom.addEventListener('pointerup', (e) => {
    if (!down || Math.hypot(e.clientX - down[0], e.clientY - down[1]) > 5) { down = null; return; } down = null;
    const r = dom.getBoundingClientRect(); v2.set(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
    ray.setFromCamera(v2, st.camera); grp.updateMatrixWorld(true);
    const hit = ray.intersectObjects(spheres, false);
    if (hit.length) { const i = hit[0].object.userData.i; sel = [sel[1], i]; restyle(); }
  });
  build(); relabel();
}
