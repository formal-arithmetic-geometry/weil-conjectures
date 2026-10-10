1. Files written:

   - `dag/nodes/sec-abelian-varieties/lem-sp-edge-collapse.json`: statement, no new child nodes, Mathlib searches recorded as no match (LeanSearch unavailable).
   - `citations.json`: verbatim citations for the sole proof step.

2. Attachments: none.

3. WANTED: none.

4. Problems found: the imported node was unsplit and had no recorded Mathlib searches. I retained its statement and made its status `split`; no existing Lean declaration carries the blueprint tag or states this result. The unit and blueprint paths in the imported metadata refer to generated blueprint material not present as checked-in files, so the imported node's source metadata is retained.

## Review by K1

I read the item statement and proof paragraph, then opened `def-sp-exact-couple.json` and `def-sp-convergence.json`. The exact-couple statement gives the recursive page formula and the differential bidegree `(r,1-r)` (via `d_r = g_r \\circ f_r`), which is exactly what Step 1 uses to place every outgoing differential from column 0 in a positive column and every incoming differential into column 0 from a negative column. The convergence statement supplies the cycle/boundary limit `E_\\infty`, the canonical identification `E_\\infty^{p,q} \\cong \\operatorname{gr}^p A^{p+q}`, and the exhaustive/separated filtration conditions used in the same step.

The hypothesis `E_{r_0}^{p,q}=0` for `p != 0` was checked directly against those bidegrees: for `p=0`, both source and target of a differential vanish; for `p>0` the source is already zero when considering incoming maps, and for `p<0` the term itself is zero. Therefore page cohomology leaves every page equal to `E_{r_0}`. Since all graded pieces except `p=0` vanish, the finite exhaustive separated filtration gives `F^0A^n=A^n` and `F^1A^n=0`; the convergence isomorphism then gives the stated edge isomorphism (in the direction `A^n -> E_{r_0}^{0,n}` by inversion). I checked the degenerate cases `E_{r_0}=0` and a filtration concentrated in degree zero; both satisfy the argument. No additional lemma is needed, so no child node was created.

5. What I could not finish: nothing. The required dry run is the remaining verification step.

## Second reading by K1

- Item statement: checked against the imported blueprint node lem-sp-edge-collapse, including the exact-couple, convergence, and finite-filtration hypotheses; verdict: correct, with the filtration definition now cited explicitly.
- Step 1: checked against def-sp-exact-couple (differential bidegree and page quotient), def-sp-convergence (recursive cycles/boundaries and the E-infinity to graded-piece isomorphism), and def-sp-filtration (finite bounds and graded pieces); verdict: the stated bidegree argument, page stabilization, limiting-page identification, and edge-map direction are valid under the hypotheses.
- New nodes: none; no auxiliary fact was needed beyond the cited definitions and the written filtration argument.
- Mathlib and duplicate searches: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches were checked against searches.jsonl; no Mathlib declaration or existing duplicate supplies this exact edge-collapse result.
- Small cases and hypotheses: the zero spectral sequence and a filtration concentrated in degree zero satisfy the argument; the proof uses only the stated exact-couple, convergence, and finite exhaustive separated filtration hypotheses.

Changes made: added def-sp-filtration to the statement, step dependencies, and citations; filled the blueprint proof place; and documented the second-reader checks above.
