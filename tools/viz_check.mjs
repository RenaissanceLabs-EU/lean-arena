// Headless check of one visualization.
//   node tools/viz_check.mjs <id> [--out /tmp/viz-shots]
// Serves docs/, opens /viz/test.html?id=<id> in Chrome (software WebGL), then:
//   - fails on any console error, page error or runtime error
//   - screenshots in light and dark, and after moving every slider to min and max, pressing every
//     button, trying every select option and dragging on the stage
//   - fails if the stage looks blank (fewer than 0.5% of pixels differ from the corner colour)
// Exit code 0 = pass. Screenshots are written to --out (default /tmp/viz-shots).
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import puppeteer from './node/node_modules/puppeteer-core/lib/esm/puppeteer/puppeteer-core.js';
import { PNG } from './node/node_modules/pngjs/lib/png.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const docs = path.join(here, '..', 'docs');
const vizSrc = path.join(here, '..', 'viz');
const three = path.join(here, 'node', 'node_modules', 'three');
const id = process.argv[2];
const out = process.argv.includes('--out') ? process.argv[process.argv.indexOf('--out') + 1] : '/tmp/viz-shots';
if (!id) { console.error('usage: node tools/viz_check.mjs <id>'); process.exit(2); }
fs.mkdirSync(out, { recursive: true });
const types = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.woff2': 'font/woff2', '.json': 'application/json' };
const server = http.createServer((req, res) => {
  let p = decodeURIComponent(req.url.split('?')[0]);
  if (p.endsWith('/')) p += 'index.html';
  // visualizations are served from source, so nobody has to rebuild the shared site to test one
  let root = docs, rel = p;
  if (p.startsWith('/viz/')) { root = vizSrc; rel = p.slice(4); }
  else if (p === '/assets/three.module.min.js') { root = path.join(three, 'build'); rel = '/three.module.min.js'; }
  else if (p === '/assets/OrbitControls.js') { root = path.join(three, 'examples', 'jsm', 'controls'); rel = '/OrbitControls.js'; }
  const f = path.join(root, rel);
  if (!f.startsWith(root) || !fs.existsSync(f)) { res.writeHead(404); return res.end('not found'); }
  res.writeHead(200, { 'content-type': types[path.extname(f)] || 'application/octet-stream' });
  fs.createReadStream(f).pipe(res);
});
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const port = server.address().port;

const browser = await puppeteer.launch({
  executablePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless: 'new',
  args: ['--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist', '--no-sandbox'],
});
const problems = [];
let shots = 0;
const wait = (ms) => new Promise((r) => setTimeout(r, ms));

async function run(dark, width) {
  const page = await browser.newPage();
  await page.setViewport({ width, height: 900, deviceScaleFactor: 1 });
  page.on('console', (m) => { if (m.type() === 'error') problems.push('console error: ' + m.text()); });
  page.on('pageerror', (e) => problems.push('pageerror: ' + e.message));
  await page.goto(`http://127.0.0.1:${port}/viz/test.html?id=${encodeURIComponent(id)}${dark ? '&dark=1' : ''}`, { waitUntil: 'load' });
  try { await page.waitForFunction('window.__viz && window.__viz.ready', { timeout: 15000 }); } catch { problems.push('never became ready'); }
  await wait(1200);
  const stage = await page.$('.vz-stage');
  if (!stage) { problems.push('no .vz-stage'); await page.close(); return; }
  const box = await stage.boundingBox();

  async function snap(tag) {
    const file = path.join(out, `${id}-${width}${dark ? '-dark' : ''}-${tag}.png`);
    await stage.screenshot({ path: file });
    shots++;
    const png = PNG.sync.read(fs.readFileSync(file));
    const { width: w, height: h, data } = png;
    const bg = [data[0], data[1], data[2]];
    let diff = 0;
    for (let i = 0; i < w * h; i++) {
      const o = i * 4;
      if (Math.abs(data[o] - bg[0]) + Math.abs(data[o + 1] - bg[1]) + Math.abs(data[o + 2] - bg[2]) > 24) diff++;
    }
    const frac = diff / (w * h);
    if (frac < 0.005) problems.push(`${tag} (${width}px${dark ? ', dark' : ''}) looks blank: ${(frac * 100).toFixed(2)}% non-background`);
  }

  await snap('start');
  if (!dark && width > 600) {
    const nSliders = (await page.$$('.vz-controls input[type=range]')).length;
    for (let i = 0; i < nSliders; i++) {
      for (const pos of [0, 1, 0.5]) {
        await page.evaluate((i, pos) => {
          const s = document.querySelectorAll('.vz-controls input[type=range]')[i];
          s.value = +s.min + pos * (+s.max - +s.min);
          s.dispatchEvent(new Event('input', { bubbles: true }));
        }, i, pos);
        await wait(250);
        if (pos !== 0.5) await snap(`slider${i}-${pos}`);
      }
    }
    const buttons = await page.$$('.vz-controls .vz-btn');
    for (let i = 0; i < buttons.length; i++) { await buttons[i].click(); await wait(700); await snap(`button${i}`); }
    const nSelects = (await page.$$('.vz-controls select')).length;
    for (let i = 0; i < nSelects; i++) {
      const opts = await page.evaluate((i) => Array.from(document.querySelectorAll('.vz-controls select')[i].options).map((o) => o.value), i);
      for (const v of opts) {
        await page.evaluate((i, v) => {
          const s = document.querySelectorAll('.vz-controls select')[i];
          s.value = v;
          s.dispatchEvent(new Event('change', { bubbles: true }));
        }, i, v);
        await wait(300);
        await snap(`select${i}-${v}`);
      }
    }
    await page.mouse.move(box.x + box.width * 0.5, box.y + box.height * 0.5);
    await page.mouse.down();
    await page.mouse.move(box.x + box.width * 0.62, box.y + box.height * 0.45, { steps: 6 });
    await page.mouse.up();
    await wait(300);
    await snap('after-drag');
  }
  const errs = await page.evaluate('window.__viz.errors');
  errs.forEach((e) => problems.push('runtime: ' + e));
  await page.close();
}

await run(false, 1100);
await run(true, 1100);
await run(false, 390);
await browser.close();
server.close();
if (problems.length) {
  console.log(`FAIL ${id}`);
  [...new Set(problems)].slice(0, 12).forEach((p) => console.log('  - ' + p));
  process.exit(1);
}
console.log(`PASS ${id} (${shots} screenshots in ${out})`);
