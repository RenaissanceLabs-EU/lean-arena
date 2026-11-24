# Writing an area page

The site math.renaissancelabs.eu maps all of mathematics using the 63 top-level areas of the Mathematics Subject Classification (MSC2020). `data/msc.json` has the official code, name and subareas of each. You write one file per area: `data/areas/<code>.json`.

Readers: a curious adult or student who wants to know what the area is about, and a researcher scanning for accuracy. Every sentence must survive a specialist reading it. When unsure of a hypothesis, date or attribution, say less rather than risk being wrong.

## Schema (all keys required)

```json
{
  "code": "11",
  "short": "Number theory",
  "hook": "Which whole numbers are sums of two squares, and why do primes thin out the way they do?",
  "about": ["First paragraph, 45 to 75 words: what the area studies, in plain words.", "Second paragraph, 45 to 75 words: its methods, flavor and how it connects to the rest of mathematics."],
  "example": {"title": "A first taste", "text": "40 to 80 words: one concrete small example or question a student can follow, with the actual numbers or objects."},
  "objects": [{"term": "Prime number", "gloss": "A whole number above 1 divisible only by 1 and itself."}],
  "theorems": [{"name": "Quadratic reciprocity", "year": 1796, "statement": "For distinct odd primes \\(p\\) and \\(q\\), ..."}],
  "open": [{"name": "Riemann hypothesis", "gloss": "One sentence on what is asked."}],
  "uses": ["Public-key cryptography", "Error-correcting codes"],
  "links": ["14", "12", "05"]
}
```

- `short`: a label of at most 24 characters for a map, sentence case. Use the official name when it fits.
- `hook`: one sentence or question, at most 130 characters, concrete, no jargon.
- `objects`: 5 to 7 central objects or ideas; gloss at most 18 words.
- `theorems`: 4 to 6 landmark results that a specialist would agree are central. `statement` is one or two sentences and must be mathematically correct with its hypotheses. `year` is an integer only if you are certain, else `null`. For areas that are applications (70 to 97) or meta (00, 01, 97), "theorems" may be central results, models, equations or methods (for example the Navier-Stokes equations), stated accurately.
- `open`: 0 to 3 well-known open problems or active frontiers. Do not list something as open if it has been solved.
- `uses`: 2 to 4 short phrases naming where the area shows up outside itself.
- `links`: 3 to 6 codes of the most closely related MSC areas (two-digit strings that exist in `data/msc.json`, not the area itself).

## Style

- Mathematics goes in LaTeX between `\(` and `\)` (in JSON: `\\(` and `\\)`). Keep formulas short. Only standard LaTeX that KaTeX renders. No `$`.
- American spelling. Short plain sentences. No em dashes, no emoji, no exclamation marks, no hype words (fascinating, beautiful, powerful, elegant, rich, deep, crucial).
- Do not say anything about whether results are formalized in Lean or any proof assistant; that data comes from elsewhere.
- No living persons except as the standard name of a theorem.

## Check

Run `python3 tools/check_areas.py <code> <code> ...` on your codes. It must print `ok` for each. Then reread every theorem statement once more as a hostile specialist and fix anything loose. Report back only: the codes written, and any statement you remain unsure of.
