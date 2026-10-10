# Stage-1 report: lem-pc-curve-coherent-finiteness

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-curve-coherent-finiteness.json`: item split into three proof steps; no new child node.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H` belongs to `lem-pc-cohomology-sections-affine-base` (the node states the affine-base cohomology/higher-direct-image isomorphism).
- `AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage` belongs to `lem-pc-coherent-hi` (the node states coherence and finite affine-base cohomology for proper morphisms over locally Noetherian schemes).
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` belongs to `lem-sc-noetherian-cohomology-above-dimension` (the node states vanishing above topological Krull dimension).

## WANTED

None.

## What was checked and corrected

The imported item was checked against the blueprint proof in `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-coherence/lem-pc-curve-coherent-finiteness.md` and against `WeilConjectures/AlgebraicGeometry/Cohomology/ProjectiveLine.lean`, lines 273–301. The slopmaster2 declaration is sorry-free but has an explicit dimension hypothesis, finite projective embedding, and `Subsingleton` vanishing conclusion, so it is not an exact attachment to the natural-language item. Its audit opens three sorry-backed declarations; each was matched to an existing DAG node rather than duplicated.

## Review by M1

I read the finite-projection source used in step 1 and the statements of `lem-pc-projective-curve-finite-projection`, `pqf-lem-coherent-ft-locnoeth`, and `lem-pc-coherent-hi`. Step 1 uses the finite map to `\\mathbf P^1`, the affine coherence criterion, and the proper higher-direct-image coherence/finite-module statement; the hypotheses (finite implies proper, `\\mathbf P^1_k` locally Noetherian, and the restriction of a coherent sheaf) are those in the item setting.

For step 2 I read `pqf-lem-affine-vanishing`, `pqf-lem-leray`, and `lem-pc-cohomology-sections-affine-base`. Their statements respectively give affine acyclicity, the Leray spectral sequence, and the affine-base identification with higher-direct-image sections. The inverse image of an affine under the finite morphism is affine, so the vanishing hypothesis is met; the extra comparison citation records the audited Lean declaration without changing the argument.

For step 3 I read the two projective-line nodes and `lem-sc-noetherian-cohomology-above-dimension`. The former give finite-dimensionality in degrees 0 and 1 and vanishing from degree 2; the latter supplies the attached general dimension-vanishing declaration, applied to the Noetherian projective line of dimension one. I checked the edge cases `i=0`, `i=1`, and `i=2` (the first two are finite-dimensional and the last is already in the vanishing range). No statement was changed, no duplicate node was needed, and all citation quotes are verbatim in `citations.json`.

## What could not be finished

Nothing; the dry-run checks are the remaining validation step.

## Second reading by M1

- Item statement: checked against the blueprint lemma and the slopmaster2 curve-cohomology interface; the hypotheses and conclusions agree, including degrees 0, 1, and >=2.
- Step 1: checked the finite projection node, the locally Noetherian coherence criterion, and the proper direct-image coherence node; finite-over-the-base generators and principal-open localization are now explicit.
- Step 2: checked affine vanishing, the affine-base higher-direct-image sections isomorphism, and Leray; the argument now explicitly vanishes sections on the affine basis before applying spectral-sequence degeneration.
- Step 3: checked the projective-line finite-dimensionality and vanishing nodes and the dimension-vanishing attachment; the cases i=0, i=1, and i>=2 match the item.
- New nodes: none; no new statement required B1-B7 or a Mathlib search.
- Edge cases: the zero sheaf gives zero groups, a field-valued point has only degree-zero cohomology, and the empty scheme is covered by the dimension-vanishing convention.

Changes made: expanded Step 1's restriction-map argument and Step 2's affine-basis vanishing argument to remove compressed “same calculation” and “therefore” gaps; no statements or citations were changed.
