Files written:

- `dag/nodes/sec-picard-framework/lem-pc-proper-direct-image-finite-tor.json` — item split, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.

Attachments: none.

WANTED: none.

The item was not present as a sorry-free declaration in `WeilConjectures/`; the source search found no declaration tagged `lem-pc-proper-direct-image-finite-tor`. I found no existing DAG node duplicating the finite-Tor direct-image statement. The proof follows Stacks Tag 08EV, using the already split nodes for the uniform direct-image truncation bound, K-flat resolutions, termwise derived pullback, projection formula, and derived base change. No new node was needed.

Mathlib searches run for the item:

- `leanfinder`: `proper direct image of bounded coherent complex with finite Tor dimension has finite Tor dimension`; hits were generic algebraic-geometry compactness lemmas and no direct-image/Tor theorem; verdict `no match`.
- `loogle`: `DerivedCategory finiteTorAmplitude Rf_*`; service returned zero hits with a pattern parse error; verdict `unavailable`.
- `grep`: `finiteTorDim|finiteTorAmplitude|tor amplitude` in `Mathlib/AlgebraicGeometry`; zero hits; verdict `no match`.

## Review by H1

I read the item statement and its Tag 08EV source reference, then read the statements of every cited DAG node. Step 1 uses the uniform truncation-bound statement, which supplies a single cohomological bound after the proper-support reduction to a quasi-compact morphism. Step 2 uses the K-flat-resolution statement and the termwise derived-pullback statement; their hypotheses match the arbitrary module and bounded-above flat resolution used there. Step 3 uses the projection-formula statement and the derived base-change statement exactly for the displayed tensor/direct-image comparison, together with the same uniform truncation bound. Step 4 is only the definition of finite Tor dimension. Every citation is represented by a verbatim quote in `citations.json`.

I checked the hypotheses explicitly: S is Noetherian as required by Tag 08EV; proper supports permit the quasi-compact restriction; E is bounded with coherent cohomology and has one finite Tor interval independent of the test module; and the K-flat resolution supplies the flat complex needed by the pullback/base-change statement. Small edge cases checked were f the identity (the conclusion reduces to the assumed finite Tor interval), E=0 (any interval works), and F=0 (the tensor complex vanishes). I corrected the original unsplit item by adding the complete four-step proof, its proof dependencies, proof origin, split report, and the required search records; no duplicate or auxiliary clause node was created.

## Second reading by H1

- Item statement: checked against Stacks Tag 08EV, Lemma 36.27.1; hypotheses and finite-Tor conclusion agree, including the zero-complex and identity-morphism cases.
- Step 1: checked against the Tag 08EV proper-support reduction and the uniform truncation node; the quasi-compact restriction and its unchanged direct image are the stated reduction.
- Step 2: checked against Tag 08EV and the bounded-flat replacement, K-flat/pullback nodes; repaired the unsupported claim that an arbitrary K-flat resolution is bounded above.
- Step 3: checked against the Tag 08EV projection-formula calculation and uniform truncation node; added the derived-direct-image definition for the lower-bound argument and made the shift explicit.
- Step 4: checked against the definition of finite Tor dimension; elementary conclusion from the common interval.
- New nodes: none; therefore B1-B7 and duplicate/mathlib-node checks are vacuous. Existing cited nodes were read and their statements match the uses; searches recorded in `searches.jsonl` were rerun and retained.
- Changes: corrected `created.item` to this item, added `lem-pc-kflat-bounded-flat-replacement` and `def-pc-derived-direct-image` to the proof dependencies and citations, and rewrote Steps 2-3 to state the missing constructions and bounds.
