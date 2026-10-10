Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-enough-globally-generated-ample.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-finite-sections-cover-qc.json` (statement-only child; no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-tensor-globally-generated.json` (statement-only child; no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-tensor-section-affine-open.json` (statement-only child; no Mathlib match).

Attachments: none.

WANTED: none; the Stacks source was consulted online at tag 09NC because the local literature checkout contains only citation indexes.

The item was unsplit. I split the proof at the four mathematical moves in Stacks 09NC: finite principal-open reduction by quasi-compactness, finite global generators, tensor-product global generation, and the affine tensor-section criterion followed by the definition of ampleness. The three auxiliary facts are strictly smaller statement-only nodes and were searched across the DAG, blueprint, and Lean/Mathlib source before creation.

Nothing remained unfinished. No source statement was found to be false; the edge cases of an affine scheme (one principal open), an empty tensor index choice, and a point lying in exactly one selected affine principal open are consistent with the construction.

## Review by K1

I read the item and its source, Stacks Varieties Lemma 09NC, including the displayed tensor construction and the invocation of Properties Lemma 28.27.4. I also read the statements of `def-weil-pbc-quasi-compact-scheme`, `def-weil-pbc-generating-sections`, `def-sc-invertible-module`, and `def-weil-pbc-ample-invertible-module`. Step 1 uses only the quasi-compact statement that every open cover has a finite subcover. Step 2 uses the new finite-section node, whose statement is exactly the finite family of nonvanishing opens, together with the existing global-generation and principal-open definitions. Step 3 uses the new tensor-global-generation statement and the existing invertibility definition. Step 4 uses the new tensor-section affine-open statement and the exact ample definition; its cover argument chooses nonvanishing sections pointwise and replaces one factor by the distinguished affine section without losing nonvanishing.

For each new node I searched `dag/nodes`, the complete blueprint index via `tools/blueprint_refs.py`, the slopmaster2 Lean source, and Mathlib by LeanSearch, LeanFinder, and source grep; no exact declaration was found. Each new node is statement-only as required, has a self-contained statement and hypotheses, records its Stacks source and blueprint ancestry, and has no proof sketch. I checked the small affine and one-point-cover cases while checking that the finite-section and tensor statements do not add hypotheses.
