1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-ample-proj-canonical-map.json`: statement split; no new nodes and no Mathlib leaves.
   - `citations.json`: verbatim statement quotes for every cited node in every proof step.

2. Attachments: none.

3. WANTED: none.

4. The item was unsplit. I kept its statement unchanged and supplied the missing proof through the local chart construction of Properties Lemma 01PZ and Constructions Lemma 01N8. No duplicate node was created: a child stating the canonical map would restate the item. The Mathlib construction `Proj.fromOfGlobalSections` applies only to the trivial structure sheaf and is not an exact attachment.

5. What I could not finish: nothing.

## Review by G1

I read the item source, Properties Lemma 01PZ (`properties.tex`, label `lemma-map-into-proj`), and the cited construction in Constructions Lemma 01N8. The statement agrees with 01PZ's hypotheses and clauses: an invertible module, the section ring, a cover by positive-degree nonvanishing opens, the canonical map, inverse images of `D_+(s)`, and the induced localization map. I also read the statements of `def-pc-proj`, `lem-weil-pbc-nonvanishing-section-trivializes`, `lem-weil-pbc-morphism-into-affine-scheme`, and `lem-weil-pbc-scheme-morphism-gluing` before citing them.

Step 1 uses the nonvanishing-trivialization statement for the unit on `X_s`, the affine morphism/ring-map correspondence to obtain `f_s`, and the Proj chart statement `D_+(s)=Spec(S_(s))`; each cited statement contains exactly that fact. Step 2 checks the overlap formula by the localization fraction calculation, with the unit property supplied by the nonvanishing-trivialization statement; the remaining equality is elementary. Step 3 applies the cited open-cover gluing theorem to the cover assumed in the item. Step 4 checks both inclusions of the inverse image using the local chart maps and the quotient `s/t`, then reads the section-ring map directly from the definition in Step 1; the Proj chart and trivialization statements supply the cited hypotheses.

I checked the small cases `s=0` (empty nonvanishing open and empty standard chart) and `\mathcal L=\mathcal O_X` (the usual construction from a graded ring map to global functions). I searched the whole DAG for 01PZ, 01N8, section-ring, and Proj-chart statements; only the existing generic affine and gluing infrastructure was suitable, so no new node was introduced. Mathlib searches were run for LeanFinder, Loogle, grep, and LeanSearch; the results showed only the trivial-bundle `Proj.fromOfGlobalSections` family or unavailable service, so the item remains non-Mathlib.

## Second reading by G1

Item statement: checked against `properties.tex` 01PZ (`lemma-map-into-proj`) and `constructions.tex` 01N8 (`lemma-converse-construction`): scheme, invertible module, graded section ring, and positive-degree nonvanishing cover agree with 01PZ; the inverse-image clause is 01PZ(1), while the local fraction formula is in the proof of 01N8, not 01PZ(3). The requested clauses are valid on the empty scheme, for the zero section (both opens empty), and for the trivial invertible module.

Step 1: checked against the local-map paragraph of 01N8 and the exact statements of the nonvanishing-trivialization, affine-morphism, and Proj-chart nodes; the section of degree `nd` divided by the `n`th power of a degree-`d` section has degree zero. Pass.

Step 2: checked against the overlap paragraph of 01N8, with the cited affine inverse-image and Proj-chart statements; for degrees `d` and `e`, `t^d/s^e` detects the overlap, and both maps on `S_(st)` send `xi/(st)^n` to the same quotient. Pass after repair.

Step 3: checked against 01N8's gluing paragraph and the cited scheme-morphism-gluing node; the assumed opens cover, and Step 2 supplies compatibility. Pass.

Step 4: checked against 01PZ(1), 01N8's local formula, and the cited affine inverse-image, Proj-chart, and nonvanishing-trivialization statements; `s^e/t^d` detects `X_s` on the `t` chart, including degrees 1 and 2. Pass after repair.

New nodes: none. I checked for a duplicate 01PZ or section-ring node in the DAG; `lem-sc-ample-proj-local-chart` uses this item and cannot replace it without a cycle. The generic Mathlib Proj construction does not state the invertible-module result, so no new Mathlib leaf is justified.

Changes: repaired Steps 2 and 4 for sections of unequal degrees and made their inverse-image citations explicit; spelled out both restriction maps on the overlap and marked Step 2 non-elementary; corrected the source attribution of the local formula; updated `citations.json` for the added cited statements. The generic affine, gluing, and trivialization nodes remain declared in `split_report.tool_uses` as required by `SETUP.md`; no curve-estimate node supplies them. The original `## Review by G1` above is retained as the first reader's record; its shorthand `s/t` and attribution of the local formula to 01PZ(3) are superseded here.
