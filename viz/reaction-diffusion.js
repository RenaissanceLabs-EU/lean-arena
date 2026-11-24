// Mathematical biology: the Gray-Scott reaction-diffusion model on a 128 x 128 periodic grid.
//   U' = Du lap(U) - U V^2 + F (1 - U),   V' = Dv lap(V) + U V^2 - (F + k) V
// Explicit Euler step with dt = 1, grid spacing 1 and the 5-point Laplacian. Stability: dt * D * 4 <= 1 for each
// diffusion constant; here 4 * 0.16 = 0.64 < 1 (the reaction terms are mild at these rates), so the step is stable.
export default function mount(root, ctx) {
  const T = ctx.THREE;
  const st = ctx.stage({ ortho: true, rotate: false, controls: false, height: 4.2, pos: [0, 0, 10] });
  const N = 128, DU = 0.16, DV = 0.08, SIDE = 4.0;
  const presets = {
    spots:   { name: 'Spots', F: 0.030, k: 0.062 },
    stripes: { name: 'Stripes and worms', F: 0.040, k: 0.063 },
    mitosis: { name: 'Mitosis-like (splitting spots)', F: 0.0367, k: 0.0649 },
    coral:   { name: 'Coral', F: 0.0545, k: 0.062 },
  };
  let F = presets.spots.F, K = presets.spots.k, steps = 0, running = !ctx.reduced, spf = 14, ms = 4;
  let U = new Float32Array(N * N), V = new Float32Array(N * N), U2 = new Float32Array(N * N), V2 = new Float32Array(N * N);
  const xm = new Int32Array(N), xp = new Int32Array(N); for (let i = 0; i < N; i++) { xm[i] = (i + N - 1) % N; xp[i] = (i + 1) % N; }
  let seed = 7; const rnd = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 4294967296; };

  function step() {
    for (let y = 0; y < N; y++) {
      const ym = xm[y] * N, yp = xp[y] * N, yy = y * N;
      for (let x = 0; x < N; x++) {
        const i = yy + x, a = yy + xm[x], b = yy + xp[x], u = U[i], v = V[i];
        const lu = U[a] + U[b] + U[ym + x] + U[yp + x] - 4 * u, lv = V[a] + V[b] + V[ym + x] + V[yp + x] - 4 * v, r = u * v * v;
        U2[i] = u + DU * lu - r + F * (1 - u); V2[i] = v + DV * lv + r - (F + K) * v;
      }
    }
    let t = U; U = U2; U2 = t; t = V; V = V2; V2 = t; steps++;
  }
  function reset() {
    U.fill(1); V.fill(0); seed = 7; steps = 0;
    for (let q = 0; q < 6; q++) { const cx = 16 + Math.floor(rnd() * (N - 32)), cy = 16 + Math.floor(rnd() * (N - 32)), s = 5 + Math.floor(rnd() * 4);
      for (let y = -s; y < s; y++) for (let x = -s; x < s; x++) { const i = (cy + y) * N + cx + x; U[i] = 0.5; V[i] = 0.25; } }
    for (let i = 0; i < N * N; i++) { U[i] += 0.02 * (rnd() - 0.5); V[i] += 0.02 * (rnd() - 0.5); }
    for (let i = 0; i < (ctx.reduced ? 3000 : 400); i++) step(); // head start so a pattern shows at once
    paint(); showStats();
  }

  const lut = new Uint8Array(256 * 3), px = new Uint8Array(N * N * 4);
  const tex = new T.DataTexture(px, N, N, T.RGBAFormat); tex.magFilter = T.LinearFilter; tex.minFilter = T.LinearFilter; tex.colorSpace = T.SRGBColorSpace; tex.needsUpdate = true;
  const plane = new T.Mesh(new T.PlaneGeometry(SIDE, SIDE), new T.MeshBasicMaterial({ map: tex })); st.scene.add(plane);
  function paint() {
    for (let i = 0; i < N * N; i++) { const q = Math.min(255, Math.max(0, Math.round(V[i] / 0.4 * 255))) * 3; px[i * 4] = lut[q]; px[i * 4 + 1] = lut[q + 1]; px[i * 4 + 2] = lut[q + 2]; px[i * 4 + 3] = 255; }
    tex.needsUpdate = true; ctx.invalidate();
  }
  ctx.onTheme((p) => { // V = 0 is the paper color, then teal, then gold for the highest V
    const a = ctx.color(p.dark ? '#14171c' : p.paper), b = ctx.color(p.c2), c = ctx.color(p.c1), o = new T.Color(), rgb = { r: 0, g: 0, b: 0 };
    for (let i = 0; i < 256; i++) { const t = i / 255; if (t < 0.5) o.copy(a).lerp(b, t * 2); else o.copy(b).lerp(c, (t - 0.5) * 2);
      o.getRGB(rgb, T.SRGBColorSpace); lut[i * 3] = Math.round(rgb.r * 255); lut[i * 3 + 1] = Math.round(rgb.g * 255); lut[i * 3 + 2] = Math.round(rgb.b * 255); }
    paint();
  });

  const fOut = ctx.ui.readout({ label: 'Feed F, kill k' }), sOut = ctx.ui.readout({ label: 'Steps' });
  function showStats() { fOut.set(F.toFixed(4) + ', ' + K.toFixed(4)); sOut.set(String(steps)); }
  const sel = ctx.ui.select({ label: 'Pattern', options: Object.entries(presets).map(([k, v]) => [k, v.name]), value: 'spots', onChange: (k) => { F = presets[k].F; K = presets[k].k; reset(); } });
  ctx.ui.button({ label: 'Reset', onClick: reset });
  const pb = ctx.ui.button({ label: running ? 'Pause' : 'Play', onClick: () => { running = !running; pb.el.textContent = running ? 'Pause' : 'Play'; } });

  let t0 = 0, tick = 0;
  ctx.loop(() => {
    if (!running) return;
    t0 = performance.now(); for (let i = 0; i < spf; i++) step(); paint();
    const dt = performance.now() - t0; ms = 0.8 * ms + 0.2 * dt; // adapt: aim for about 10 ms of work per frame
    spf = Math.max(2, Math.min(40, Math.round(spf * (ms > 12 ? 0.85 : ms < 7 ? 1.1 : 1) + (ms < 7 ? 1 : 0))));
    if (++tick % 6 === 0) showStats();
  });

  function drop(p) {
    const { w, h } = ctx.size(); const x = p.x * st.height / 2 * w / h, y = p.y * st.height / 2;
    const gx = Math.floor((x / SIDE + 0.5) * N), gy = Math.floor((y / SIDE + 0.5) * N);
    for (let dy = -4; dy <= 4; dy++) for (let dx = -4; dx <= 4; dx++) if (dx * dx + dy * dy <= 16) {
      const i = (((gy + dy + N) % N) * N) + ((gx + dx + N) % N); if (gx + dx < 0 || gx + dx >= N || gy + dy < 0 || gy + dy >= N) continue;
      U[i] = Math.min(U[i], 0.5); V[i] = Math.max(V[i], 0.25);
    }
    paint();
  }
  ctx.pointer(st.renderer.domElement, { down: drop, move: (p, d) => { if (d) drop(p); } });
  reset();
}
