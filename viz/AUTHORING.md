# Authoring a visualization

Each area page on math.renaissancelabs.eu can carry one interactive figure that gives an intuitive grasp of a core idea of that area. A figure earns its place only if it shows something prose cannot. It must feel deliberate: one idea, shown clearly, with controls that change that idea and nothing else.

Read `viz/linear-map.js` and `viz/meta/15.json` first and copy their shape. `viz/runtime.js` documents the API (`ctx`) in its header comment.

## What you write

- `viz/<id>.js`: `export default function mount(root, ctx) { ... }`. kebab-case id. One file, at most about 400 lines, no imports other than what `ctx` gives you (`ctx.THREE`, `ctx.OrbitControls`). No network, no external assets, no libraries.
- `viz/meta/<code>.json`, with the area code as the file name:

```json
{ "code": "15", "id": "linear-map", "title": "What a matrix does to space",
  "lede": "One or two sentences: what you are looking at and what the controls change.",
  "notice": ["Two or three statements, each TRUE and VISIBLE in the figure.", "..."],
  "hint": "Drag to rotate. Press Play to ..." }
```

`title` at most 60 characters. `lede` at most 200. Each `notice` item at most 200 characters, plain language, American English, no em dashes, no hype words. Mathematics in `\( \)` is allowed in title, lede and notice (KaTeX renders it); keep it short. `hint` at most 90 characters, tells the user how to interact.

Touch only your own `viz/<id>.js` and `viz/meta/<code>.json`. Do not edit `runtime.js`, `build.py`, `styles.css` or anything else, and do not run `build.py` (several people work in parallel). If you need something the runtime lacks, work around it inside your module and say so in your report.

## The quality bar

1. **One clear idea.** If you cannot say in one sentence what a person should understand after playing for 30 seconds, simplify. Two or three controls at most, plus presets. The default state must already show the idea with no interaction.
2. **Mathematically correct.** Every formula, constant and claim must be right; compute things honestly (do not fake a result with an animation). If a number is displayed, it is computed from the state of the figure. A displayed statement ("the angle sum exceeds 180 degrees") must be true for every control position. Test edge cases of your controls. Where a claim has hypotheses, the figure must stay inside them or say so.
3. **Readable.** The subject fills the stage; nothing tiny, nothing clipped at the default camera. Use `ctx.label` for any text in the scene and `ctx.ui.readout` for live numbers. Use the palette (`ctx.palette()`, restyle in `ctx.onTheme`) so both light and dark themes are legible. Colour carries meaning (one colour per concept), not decoration.
4. **Smooth and light.** Under about 60k triangles; no per-frame allocation in hot loops; fixed time step for simulations with a stable scheme (state the stability condition in a comment). Use `ctx.loop` only for things that actually animate; static scenes render on input only. Respect `ctx.reduced`: with reduced motion, nothing autoplays (start paused, offer a Play button).
5. **Works on a phone.** Stage is about 340 px tall and as narrow as 360 px wide. Pointer handling must work with touch; do not capture vertical page scroll except while the user is dragging inside the stage (the stage has `touch-action: pan-y`; for pure 2D dragging use `ctx.pointer`).
6. **No dead ends.** Controls always give a valid state. No NaN, no blank frame, no console errors.

## Checking your work (must pass)

```bash
node tools/viz_check.mjs <id>
```

It serves your source, opens the figure in headless Chrome (software WebGL), fails on any console or runtime error and on blank frames, and moves every slider to its extremes, presses every button, tries every select option, drags on the stage, and screenshots in light, dark and 390 px wide. Run it one at a time (never several Chrome instances at once). Then **look at the screenshots** in `/tmp/viz-shots/` (at least: start, one slider extreme, dark, the 390 px one) and fix anything that looks cramped, clipped, tiny, cluttered or wrong. The check passing is necessary, not sufficient: you are responsible for how it looks.

## Report

Report only: ids written, the one-sentence idea of each, anything mathematically delicate you checked and how, and anything you are not sure is correct or that you could not make work. Do not paste code.
