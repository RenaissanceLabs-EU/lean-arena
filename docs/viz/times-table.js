// Number theory: the times table mod N. Point i is joined to point (m*i) mod N on a circle of N points.
// For integer m the lines envelope a curve with m-1 cusps (m=2 cardioid, m=3 nephroid).
// For fractional m the target is the point at fractional position frac(m*i/N), so the picture morphs smoothly.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 4.5, pos: [0, 0, 10] });
  const R = 1.8, TAU = Math.PI * 2, MAXN = 360;
  let N = 200, m = 2, playing = false;

  const linePos = new Float32Array(MAXN * 6);
  const lineGeo = new T.BufferGeometry(); lineGeo.setAttribute('position', new T.BufferAttribute(linePos, 3));
  const lineMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.55 });
  const lines = new T.LineSegments(lineGeo, lineMat); lines.frustumCulled = false; st.scene.add(lines);

  const ringPts = []; for (let i = 0; i <= 180; i++) ringPts.push(R * Math.cos(i / 180 * TAU), R * Math.sin(i / 180 * TAU), 0);
  const ringMat = new T.LineBasicMaterial({ transparent: true, opacity: 0.5 });
  const ring = new T.Line(new T.BufferGeometry().setAttribute('position', new T.Float32BufferAttribute(ringPts, 3)), ringMat); st.scene.add(ring);

  const dotPos = new Float32Array(MAXN * 3), fixPos = new Float32Array(MAXN * 3);
  const dotGeo = new T.BufferGeometry(); dotGeo.setAttribute('position', new T.BufferAttribute(dotPos, 3));
  const fixGeo = new T.BufferGeometry(); fixGeo.setAttribute('position', new T.BufferAttribute(fixPos, 3));
  const dotMat = new T.PointsMaterial({ size: 4, sizeAttenuation: false });
  const fixMat = new T.PointsMaterial({ size: 10, sizeAttenuation: false });
  const dots = new T.Points(dotGeo, dotMat), fixed = new T.Points(fixGeo, fixMat);
  dots.frustumCulled = fixed.frustumCulled = false; st.scene.add(dots); st.scene.add(fixed);

  const mOut = ctx.ui.readout({ label: 'Multiplier m' });
  const nOut = ctx.ui.readout({ label: 'Points N' });
  const fOut = ctx.ui.readout({ label: 'Fixed points' });

  function fixedCount() { // i with (m-1) i = 0 (mod N), exact in hundredths of m
    const M = Math.round(m * 100) - 100, mod = 100 * N; let c = 0;
    for (let i = 0; i < N; i++) { if ((((M * i) % mod) + mod) % mod === 0) { fixPos[c * 3] = R * Math.cos(i / N * TAU); fixPos[c * 3 + 1] = R * Math.sin(i / N * TAU); fixPos[c * 3 + 2] = 0.01; c++; } }
    fixGeo.setDrawRange(0, c); fixGeo.attributes.position.needsUpdate = true; return c;
  }
  function update() {
    for (let i = 0; i < N; i++) {
      const a = i / N * TAU; const f = (((m * i) % N) + N) % N; const b = f / N * TAU;
      linePos[i * 6] = R * Math.cos(a); linePos[i * 6 + 1] = R * Math.sin(a); linePos[i * 6 + 2] = 0;
      linePos[i * 6 + 3] = R * Math.cos(b); linePos[i * 6 + 4] = R * Math.sin(b); linePos[i * 6 + 5] = 0;
      dotPos[i * 3] = R * Math.cos(a); dotPos[i * 3 + 1] = R * Math.sin(a); dotPos[i * 3 + 2] = 0.02;
    }
    lineGeo.setDrawRange(0, N * 2); dotGeo.setDrawRange(0, N);
    lineGeo.attributes.position.needsUpdate = true; dotGeo.attributes.position.needsUpdate = true;
    lineMat.opacity = N > 250 ? 0.4 : 0.6;
    const isInt = Math.abs(m - Math.round(m)) < 1e-9;
    mOut.set(m.toFixed(2) + (isInt ? '' : '  (not an integer)')); nOut.set(String(N));
    const c = fixedCount();
    fOut.set(c + (isInt ? '  (= gcd(m−1, N) = ' + gcd(Math.round(m) - 1, N) + ')' : ''));
    ctx.invalidate();
  }
  const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };

  const sN = ctx.ui.slider({ label: 'Modulus N', min: 10, max: MAXN, step: 1, value: N, onInput: (v) => { N = v; update(); } });
  const sM = ctx.ui.slider({ label: 'Multiplier m', min: 2, max: 100, step: 0.01, value: m, format: (v) => v.toFixed(2), onInput: (v) => { m = v; update(); } });
  const btn = ctx.ui.button({ label: 'Play', onClick: () => { playing = !playing; btn.el.textContent = playing ? 'Pause' : 'Play'; } });
  ctx.ui.button({ label: 'm = 2', onClick: () => { playing = false; btn.el.textContent = 'Play'; sM.set(2); } });
  ctx.ui.button({ label: 'm = 3', onClick: () => { playing = false; btn.el.textContent = 'Play'; sM.set(3); } });
  ctx.loop((dt) => { if (playing) { let v = sM.get() + dt * 0.35; if (v > 100) v = 2; m = v; sM.set(Math.round(v * 100) / 100); } });

  ctx.onTheme((p) => { lineMat.color.set(p.c2); ringMat.color.set(p.rule); dotMat.color.set(p.ink); fixMat.color.set(p.c1); });
  update();
}
