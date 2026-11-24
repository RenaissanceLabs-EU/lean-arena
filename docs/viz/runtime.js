// Shared runtime for the interactive visualizations on math.renaissancelabs.eu.
//
// A visualization is an ES module at /viz/<id>.js with a default export:
//
//     export default function mount(root, ctx) { ... }
//
// `root` is an empty <div> sized by the page. `ctx` gives it everything it needs (see below).
// The module may return nothing, or an object { dispose() } for extra cleanup. The runtime
// handles: renderer creation, resizing, device pixel ratio, pausing when off screen or when the
// tab is hidden, light/dark theme changes, reduced motion, and disposal.
//
//   ctx.THREE                   the three.js namespace (r170)
//   ctx.OrbitControls           the OrbitControls class
//   ctx.reduced                 true if the user prefers reduced motion: do not autoplay
//   ctx.palette()               { ink, inkSoft, paper, card, rule, gold, hue, c1..c5, dark } as CSS strings
//   ctx.color(cssString)        a THREE.Color from any CSS colour string
//   ctx.onTheme(fn)             call fn(palette) now and whenever the theme changes: restyle materials here
//   ctx.stage(opts)             create the scene: { scene, camera, renderer, controls }
//         opts.ortho   false   orthographic camera; then opts.height is the visible world height (default 4)
//         opts.fov     45      perspective field of view
//         opts.pos     [4,3,6] camera position;  opts.target [0,0,0] look-at point
//         opts.controls true   OrbitControls (rotate, zoom, pan off by default); false to disable
//         opts.rotate  true    allow rotating (set false for a flat 2D picture)
//         opts.transparent true  clear colour is transparent so the page background shows
//   ctx.loop(fn)                fn(dt, t) runs every frame while the viz is visible; the stage is rendered after it
//   ctx.invalidate()            request one render (for static scenes that change only on input)
//   ctx.ui.slider({label, min, max, step, value, format, onInput})  -> { el, get(), set(v) }
//   ctx.ui.toggle({label, value, onChange})                         -> { el, get(), set(v) }
//   ctx.ui.button({label, onClick})                                 -> { el }
//   ctx.ui.select({label, options:[[value,label],...], value, onChange}) -> { el, get(), set(v) }
//   ctx.ui.readout({label, value})                                  -> { el, set(text) }  (live numbers)
//   ctx.pointer(el, handlers)   pointer helper for 2D dragging; see below
//   ctx.size()                  { w, h } of the stage in CSS pixels
//   ctx.label(text, {size:0.3, color:'#fff', bold:false})  a THREE.Sprite that always faces the camera;
//                               sprite.userData.setText(t) / .setColor(c) change it. Position it with sprite.position.

import * as THREE from 'three';
import { OrbitControls } from '/assets/OrbitControls.js';

const reduced = matchMedia('(prefers-reduced-motion: reduce)').matches;

function cssVar(name) { return getComputedStyle(document.documentElement).getPropertyValue(name).trim(); }
function isDark() {
  const t = document.documentElement.dataset.theme;
  return t ? t === 'dark' : matchMedia('(prefers-color-scheme: dark)').matches;
}
function palette() {
  const dark = isDark();
  return {
    dark,
    ink: cssVar('--ink'), inkSoft: cssVar('--ink-soft'), paper: cssVar('--paper'), card: cssVar('--card'),
    rule: cssVar('--rule-strong'), gold: cssVar('--gold-bright'), hue: cssVar('--hue') || cssVar('--gold'),
    // five colours that read on both themes
    c1: dark ? '#e0b657' : '#b4862a', c2: dark ? '#62b0b2' : '#2f7a7c', c3: dark ? '#df7f79' : '#b5544f',
    c4: dark ? '#8399c9' : '#4f64a0', c5: dark ? '#a0af5c' : '#6b7a2d',
  };
}

const themeListeners = new Set();
let themeWatcher = false;
function watchTheme() {
  if (themeWatcher) return; themeWatcher = true;
  const fire = () => { const p = palette(); themeListeners.forEach(fn => fn(p)); };
  new MutationObserver(fire).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', fire);
}

function el(tag, cls, text) { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; }

export async function mountViz(host, id) {
  const stageEl = host.querySelector('.vz-stage');
  const controlsEl = host.querySelector('.vz-controls');
  const state = { visible: false, hidden: document.hidden, frame: 0, dirty: true, loops: [], stages: [], disposers: [], t: 0, last: 0 };
  const errors = (window.__viz = window.__viz || { ready: false, errors: [], id });
  const onError = (e) => { errors.errors.push(String(e && e.message || e)); };

  const ui = {
    slider({ label, min = 0, max = 1, step = 0.01, value = 0, format, onInput }) {
      const wrap = el('label', 'vz-ctl'); const name = el('span', 'vz-name', label); const val = el('output', 'vz-val');
      const input = el('input'); input.type = 'range'; input.min = min; input.max = max; input.step = step; input.value = value;
      const fmt = format || ((v) => (Math.abs(step) >= 1 ? String(Math.round(v)) : (+v).toFixed(2)));
      const upd = () => { val.textContent = fmt(+input.value); };
      input.addEventListener('input', () => { upd(); onInput && onInput(+input.value); state.dirty = true; });
      wrap.append(name, input, val); controlsEl.append(wrap); upd();
      return { el: wrap, get: () => +input.value, set: (v) => { input.value = v; upd(); onInput && onInput(+input.value); state.dirty = true; } };
    },
    toggle({ label, value = false, onChange }) {
      const wrap = el('label', 'vz-ctl vz-tog'); const input = el('input'); input.type = 'checkbox'; input.checked = value;
      wrap.append(input, el('span', 'vz-name', label)); controlsEl.append(wrap);
      input.addEventListener('change', () => { onChange && onChange(input.checked); state.dirty = true; });
      return { el: wrap, get: () => input.checked, set: (v) => { input.checked = v; onChange && onChange(v); state.dirty = true; } };
    },
    button({ label, onClick }) {
      const b = el('button', 'vz-btn', label); b.type = 'button';
      b.addEventListener('click', () => { onClick && onClick(); state.dirty = true; }); controlsEl.append(b); return { el: b };
    },
    select({ label, options, value, onChange }) {
      const wrap = el('label', 'vz-ctl'); const name = el('span', 'vz-name', label); const s = el('select', 'vz-sel');
      options.forEach(([v, t]) => { const o = el('option', null, t); o.value = v; s.append(o); }); s.value = value != null ? value : options[0][0];
      s.addEventListener('change', () => { onChange && onChange(s.value); state.dirty = true; });
      wrap.append(name, s); controlsEl.append(wrap);
      return { el: wrap, get: () => s.value, set: (v) => { s.value = v; onChange && onChange(s.value); state.dirty = true; } };
    },
    readout({ label, value = '' }) {
      const wrap = el('div', 'vz-ctl vz-read'); const name = el('span', 'vz-name', label); const val = el('output', 'vz-val', value);
      wrap.append(name, val); controlsEl.append(wrap);
      return { el: wrap, set: (t) => { val.textContent = t; } };
    },
  };

  const ctx = {
    THREE, OrbitControls, reduced, ui, palette,
    color: (c) => new THREE.Color(c),
    onTheme(fn) { themeListeners.add(fn); watchTheme(); state.disposers.push(() => themeListeners.delete(fn)); fn(palette()); state.dirty = true; },
    loop(fn) { state.loops.push(fn); },
    invalidate() { state.dirty = true; },
    size() { const r = stageEl.getBoundingClientRect(); return { w: Math.max(1, r.width), h: Math.max(1, r.height) }; },
    stage(opts = {}) {
      const o = Object.assign({ ortho: false, fov: 45, pos: [4, 3, 6], target: [0, 0, 0], controls: true, rotate: true, transparent: true, height: 4 }, opts);
      const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: o.transparent, powerPreference: 'low-power' });
      renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
      renderer.domElement.className = 'vz-canvas'; stageEl.append(renderer.domElement);
      const scene = new THREE.Scene();
      let camera; const { w, h } = ctx.size();
      if (o.ortho) { const hh = o.height / 2; camera = new THREE.OrthographicCamera(-hh * w / h, hh * w / h, hh, -hh, -100, 100); }
      else camera = new THREE.PerspectiveCamera(o.fov, w / h, 0.05, 200);
      camera.position.set(...o.pos); camera.lookAt(...o.target);
      let controls = null;
      if (o.controls) {
        controls = new OrbitControls(camera, renderer.domElement);
        controls.target.set(...o.target); controls.enableDamping = !reduced; controls.dampingFactor = 0.08;
        controls.enablePan = false; controls.enableRotate = o.rotate; controls.minDistance = 1.5; controls.maxDistance = 30;
        if (o.ortho) controls.enableZoom = false;
        controls.addEventListener('change', () => { state.dirty = true; });
        controls.update();
      }
      const st = { scene, camera, renderer, controls, ortho: o.ortho, height: o.height };
      const resize = () => {
        const { w, h } = ctx.size(); renderer.setSize(w, h, false);
        if (o.ortho) { const hh = o.height / 2; camera.left = -hh * w / h; camera.right = hh * w / h; camera.top = hh; camera.bottom = -hh; }
        else camera.aspect = w / h;
        camera.updateProjectionMatrix(); state.dirty = true;
      };
      const ro = new ResizeObserver(resize); ro.observe(stageEl); resize();
      state.disposers.push(() => { ro.disconnect(); controls && controls.dispose(); renderer.dispose(); renderer.domElement.remove(); });
      state.stages.push(st); return st;
    },
    label(text, o = {}) {
      const size = o.size || 0.3; let color = o.color || '#000'; let txt = String(text);
      const cv = document.createElement('canvas'); const g = cv.getContext('2d'); const tex = new THREE.CanvasTexture(cv);
      tex.colorSpace = THREE.SRGBColorSpace; tex.anisotropy = 4;
      const mat = new THREE.SpriteMaterial({ map: tex, depthTest: false, transparent: true });
      const sp = new THREE.Sprite(mat); sp.renderOrder = 10;
      const draw = () => {
        const px = 64, font = (o.bold ? '600 ' : '400 ') + px + 'px -apple-system, "Segoe UI", sans-serif';
        g.font = font; const w = Math.ceil(g.measureText(txt).width) + 20; cv.width = w; cv.height = px + 24;
        g.font = font; g.textBaseline = 'middle'; g.textAlign = 'center'; g.fillStyle = color; g.fillText(txt, w / 2, cv.height / 2 + 2);
        tex.needsUpdate = true; sp.scale.set(size * cv.width / cv.height, size, 1); state.dirty = true;
      };
      sp.userData.setText = (t) => { txt = String(t); draw(); };
      sp.userData.setColor = (c) => { color = c; draw(); };
      draw(); state.disposers.push(() => { tex.dispose(); mat.dispose(); }); return sp;
    },
    pointer(elm, h) {
      // Normalised pointer in [-1,1] x [-1,1] (y up) over `elm`; h = { down(p), move(p), up(p) }
      const p = (e) => { const r = elm.getBoundingClientRect(); return { x: ((e.clientX - r.left) / r.width) * 2 - 1, y: -(((e.clientY - r.top) / r.height) * 2 - 1), e }; };
      let down = false;
      elm.addEventListener('pointerdown', (e) => { down = true; elm.setPointerCapture(e.pointerId); h.down && h.down(p(e)); state.dirty = true; });
      elm.addEventListener('pointermove', (e) => { if (down || h.hover) { h.move && h.move(p(e), down); state.dirty = true; } });
      elm.addEventListener('pointerup', (e) => { down = false; h.up && h.up(p(e)); state.dirty = true; });
    },
  };

  let api;
  try {
    const mod = await import('/viz/' + id + '.js');
    api = mod.default(stageEl, ctx) || {};
  } catch (e) { onError(e); stageEl.append(el('p', 'vz-fail', 'This visualization could not start on this device.')); host.classList.add('vz-failed'); return; }
  if (!state.stages.length) onError('the visualization created no stage');

  const tick = (now) => {
    state.frame = requestAnimationFrame(tick);
    if (!state.visible || state.hidden) return;
    const dt = Math.min(0.05, (now - state.last) / 1000 || 0.016); state.last = now; state.t += dt;
    let animating = state.loops.length > 0;
    try {
      for (const fn of state.loops) fn(dt, state.t);
      for (const s of state.stages) { if (s.controls && s.controls.enableDamping) s.controls.update(); }
      if (animating || state.dirty) { for (const s of state.stages) s.renderer.render(s.scene, s.camera); state.dirty = false; }
    } catch (e) { onError(e); }
  };
  const io = new IntersectionObserver((es) => { state.visible = es[0].isIntersecting; state.last = performance.now(); state.dirty = true; }, { rootMargin: '80px' });
  io.observe(host);
  const vis = () => { state.hidden = document.hidden; state.last = performance.now(); };
  document.addEventListener('visibilitychange', vis);
  state.frame = requestAnimationFrame(tick);
  state.disposers.push(() => { cancelAnimationFrame(state.frame); io.disconnect(); document.removeEventListener('visibilitychange', vis); api.dispose && api.dispose(); });
  host.__vizDispose = () => state.disposers.forEach(f => f());
  errors.ready = true;
  host.classList.add('vz-ready');
}

// Start a visualization when its figure approaches the viewport.
export function lazyMount(host, id) {
  const go = () => mountViz(host, id).catch((e) => { (window.__viz = window.__viz || { errors: [] }).errors.push(String(e)); });
  if (new URLSearchParams(location.search).has('viznow') || !('IntersectionObserver' in window)) return go();
  const io = new IntersectionObserver((es) => { if (es[0].isIntersecting) { io.disconnect(); go(); } }, { rootMargin: '300px' });
  io.observe(host);
}
