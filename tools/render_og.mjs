// Renders HTML snippets to 1200x630 JPEGs.  node tools/render_og.mjs jobs.json outdir
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import puppeteer from './node/node_modules/puppeteer-core/lib/esm/puppeteer/puppeteer-core.js';

const [jobsFile, outDir] = process.argv.slice(2);
const jobs = JSON.parse(fs.readFileSync(jobsFile, 'utf8'));
fs.mkdirSync(outDir, { recursive: true });
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'og-'));
const browser = await puppeteer.launch({
  executablePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless: 'new',
  args: ['--allow-file-access-from-files', '--no-sandbox'],
});
const page = await browser.newPage();
await page.setViewport({ width: 1200, height: 630, deviceScaleFactor: 1 });
let n = 0;
for (const j of jobs) {
  const f = path.join(tmp, j.name + '.html');
  fs.writeFileSync(f, j.html);
  await page.goto('file://' + f, { waitUntil: 'load' });
  await page.evaluate(() => document.fonts.ready);
  await new Promise((r) => setTimeout(r, 60));
  await page.screenshot({ path: path.join(outDir, j.name + '.jpg'), type: 'jpeg', quality: 90 });
  n++;
}
await browser.close();
console.log('rendered ' + n + ' images into ' + outDir);
