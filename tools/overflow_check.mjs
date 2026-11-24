// Finds horizontal overflow on phone widths.  node tools/overflow_check.mjs [--widths 320,360,390] [path ...]
// Loads every built page (or the given paths) and reports pages whose document is wider than the viewport,
// with the elements that stick out furthest.
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
const args = process.argv.slice(2);
const wi = args.indexOf('--widths');
const widths = wi >= 0 ? args.splice(wi, 2)[1].split(',').map(Number) : [320, 360, 390];
let pages = args;
if (!pages.length) {
  pages = ['/'];
  for (const d of ['about', 'checking', 'frontier', 'environments']) pages.push('/' + d + '/');
  for (const d of fs.readdirSync(path.join(docs, 'env'))) if (fs.existsSync(path.join(docs, 'env', d, 'index.html'))) pages.push('/env/' + d + '/');
  for (const d of fs.readdirSync(path.join(docs, 'area'))) pages.push('/area/' + d + '/');
}
const browser = await puppeteer.launch({ executablePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless: 'new',
  args: ['--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--ignore-gpu-blocklist', '--no-sandbox'] });
const page = await browser.newPage();
let bad = 0;
for (const w of widths) {
  await page.setViewport({ width: w, height: 800, deviceScaleFactor: 1, isMobile: true, hasTouch: true });
  for (const p of pages) {
    await page.goto(`http://127.0.0.1:${port}${p}`, { waitUntil: 'load' });
    await new Promise((r) => setTimeout(r, 500));
    const r = await page.evaluate((w) => {
      const de = document.documentElement;
      const over = Math.max(de.scrollWidth, document.body.scrollWidth) - w;
      if (over <= 1) return { over: 0 };
      const out = [];
      for (const el of document.querySelectorAll('body *')) {
        const b = el.getBoundingClientRect();
        if (b.width && b.right > w + 1) {
          const cs = getComputedStyle(el);
          if (cs.position === 'fixed') continue;
          out.push({ sel: el.tagName.toLowerCase() + (el.className && typeof el.className === 'string' ? '.' + el.className.trim().split(/\s+/).join('.') : ''), right: Math.round(b.right), width: Math.round(b.width) });
        }
      }
      out.sort((a, b) => b.right - a.right);
      return { over, out: out.slice(0, 4) };
    }, w);
    if (r.over) { bad++; console.log(`${w}px ${p} +${r.over}px  ` + r.out.map((o) => `${o.sel}(${o.width}→${o.right})`).join('  ')); }
  }
}
await browser.close(); server.close();
console.log(bad ? `${bad} overflowing page/width combos` : 'no horizontal overflow');
process.exit(bad ? 1 : 0);
