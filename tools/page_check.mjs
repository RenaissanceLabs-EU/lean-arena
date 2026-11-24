// Loads each built area page that has a figure, in headless Chrome, and checks the figure starts without errors.
//   node tools/page_check.mjs 11 12 37     (area codes; default: every page that has .vz)
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import puppeteer from './node/node_modules/puppeteer-core/lib/esm/puppeteer/puppeteer-core.js';
const here = path.dirname(fileURLToPath(import.meta.url));
const docs = path.join(here, '..', 'docs');
const types = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.jpg': 'image/jpeg', '.woff2': 'font/woff2', '.json': 'application/json' };
const server = http.createServer((req, res) => {
  let p = decodeURIComponent(req.url.split('?')[0]);
  if (p.endsWith('/')) p += 'index.html';
  const f = path.join(docs, p);
  if (!f.startsWith(docs) || !fs.existsSync(f)) { res.writeHead(404); return res.end('nf'); }
  res.writeHead(200, { 'content-type': types[path.extname(f)] || 'application/octet-stream' });
  fs.createReadStream(f).pipe(res);
});
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const port = server.address().port;
let codes = process.argv.slice(2);
if (!codes.length) codes = fs.readdirSync(path.join(docs, 'area')).filter((c) => fs.readFileSync(path.join(docs, 'area', c, 'index.html'), 'utf8').includes('class="vz"'));
const browser = await puppeteer.launch({ executablePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless: 'new',
  args: ['--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist', '--no-sandbox'] });
let bad = 0;
for (const c of codes) {
  const page = await browser.newPage();
  await page.setViewport({ width: 1280, height: 900 });
  const errs = [];
  page.on('console', (m) => { if (m.type() === 'error') errs.push(m.text()); });
  page.on('pageerror', (e) => errs.push(e.message));
  await page.goto(`http://127.0.0.1:${port}/area/${c}/?viznow`, { waitUntil: 'load' });
  let ready = true;
  try { await page.waitForFunction('window.__viz && window.__viz.ready', { timeout: 12000 }); } catch { ready = false; }
  const fig = await page.$('.vz');
  if (fig) await fig.scrollIntoView();
  await new Promise((r) => setTimeout(r, 700));
  const runtimeErrs = ready ? await page.evaluate('window.__viz.errors') : ['never ready'];
  const katex = await page.evaluate(() => document.querySelectorAll('.vizsec .katex').length);
  const ok = ready && !errs.length && !runtimeErrs.length;
  if (!ok) bad++;
  console.log((ok ? 'ok   ' : 'FAIL ') + c + (errs.length || runtimeErrs.length ? '  ' + [...errs, ...runtimeErrs].slice(0, 3).join(' | ') : '') + `  (math in caption: ${katex})`);
  await page.close();
}
await browser.close(); server.close();
process.exit(bad ? 1 : 0);
