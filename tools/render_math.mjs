// Reads a JSON array of {tex, display} on stdin, writes a JSON array of HTML strings.
import katex from "./node/node_modules/katex/dist/katex.mjs";
let raw = "";
for await (const c of process.stdin) raw += c;
const items = JSON.parse(raw);
const out = items.map(({ tex, display }) => {
  try { return katex.renderToString(tex, { displayMode: display, throwOnError: true, strict: "ignore", output: "htmlAndMathml", trust: false }); }
  catch (e) { return "KATEX_ERROR:" + tex + ":" + e.message; }
});
process.stdout.write(JSON.stringify(out));
