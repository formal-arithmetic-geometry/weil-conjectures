1. Files written:

- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-singleton-fully-faithful-0241.json`: statement node, no new Mathlib leaf.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none. No matching declaration or blueprint node was found in the Lean source or DAG.

3. WANTED: none.

4. The source item is Stacks Project `descent.tex`, Lemma Tag 0241. I checked the item statement against its assumptions and conclusion, including the singleton fpqc cover, the induced scheme-over-S structure, the definition of descent data and its pullback. The existing node `lem-galois-fpqc-morphisms-descend` states the required bijection for morphisms after an fpqc singleton cover, so no supporting node was created. Step 1 uses the descent-datum and fibre-product definitions to identify the overlap equation. Step 2 applies the morphism-descent bijection with base `X` and cover `X' -> X`; the fpqc hypothesis is exactly the item's singleton assumption. Step 3 uses base-change stability of fpqc coverings to check the descent-data equation after pullback, then uses injectivity in the same bijection for uniqueness. I verified every citation quote is a verbatim part of its node statement and that `proof_deps` is the union of the step uses. Small cases checked: `r = id_X` gives the identity functor, and for an empty scheme all morphism sets are singleton.

5. Nothing remains unfinished.

## Review by H1

I read the item's node, `lem-galois-fpqc-refinement-fully-faithful.json`, `lem-galois-fpqc-morphisms-descend.json`, `lem-galois-fpqc-covering-base-change.json`, `def-pd-descent-datum.json`, and `def-pc-fibre-product.json`. The item source is Stacks `descent.tex`, Tag 0241; the supporting morphism-descent source is Tag 02W0 and the base-change source is Tag 022D(3). For Step 1 I checked that the cited descent-datum definition supplies the two projection pullbacks and that the fibre-product definition supplies the overlap scheme. For Step 2 I checked that the cited morphism-descent statement is a bijection onto exactly the compatible overlap morphisms, and that the item's singleton fpqc hypothesis instantiates its cover hypothesis. For Step 3 I checked the cited base-change statement supplies the induced fpqc cover on the overlap, while the descent-datum definition supplies the equation being tested; injectivity of the cited bijection gives uniqueness. I corrected the initially empty proof by making these three arguments explicit, retained the existing blueprint reference to the full-faithfulness input of `lem-galois-descent`, and added exact citation quotes.
