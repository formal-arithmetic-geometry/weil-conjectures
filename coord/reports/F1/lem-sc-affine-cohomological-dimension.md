1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-affine-cohomological-dimension.json`: statement item, split; no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for all proof dependencies.

2. Attachments

- `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` belongs to `lem-weil-pbc-etale-section-continuity`.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar` belongs to `lem-sc-affine-generic-second`.

3. WANTED:

None.

4. What was wrong in the imported material

The imported item was marked `imported` and left the two open Lean declarations unattached even though both declarations already have exact existing DAG nodes. The item also had no Mathlib search records, no completed blueprint reference, and no citation file. I changed only those bookkeeping gaps; no proof step or statement was weakened.

5. What I could not finish

Nothing.

## Review by F1

I read the item source, the unit record `dag/units/sk-prop-cd-affine.json`, and the Lean declaration in `WeilConjectures/AlgebraicGeometry/Curve/CohomologicalDimension.lean` at lines 423–438. The Lean theorem is sorry-free in its own body and has the same hypotheses and conclusion as the item, with the equivalent numerical formulation `q ≥ 2` in Lean versus `q > 1` in the natural-language statement. I also read the two open declarations: the section-continuity theorem at `Sites/SectionContinuity.lean` lines 74–102 is exactly the statement already recorded by `lem-weil-pbc-etale-section-continuity`, and the generic lower-star vanishing theorem at `Curve/Affine.lean` lines 333–353 is exactly `lem-sc-affine-generic-second`; neither warranted a duplicate node. The third open declaration, filtered cohomology in `Curve/Reductions.lean` lines 68–86, is already attached to `lemma-weil-pbc-curve-filtered-cohomology`.

The sole proof step was checked against each cited statement. The cohomological-dimension node supplies vanishing for `q > 2`; the generic-comparison node supplies the isomorphism `H^q(C,F) ≅ H^q(C,η_*η^*F)` for `q ≥ 2`; and the affine-generic-second node supplies `H²(C,η_*M)=0` for torsion `M`, applied to `M = η^*F`. The degree-two hypotheses match the smooth integral affine connected curve setting supplied by the theorem, while the higher-degree clause is the connected smooth curve case. The three citations in `citations.json` are copied verbatim from the cited node statements. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was recorded as unavailable, and the other searches found no matching Mathlib étale cohomology theorem.

## Second reading by F1

- Item statement: checked against Stacks Theorem 59.83.10, Tag 03SC, assertion (2); the smooth affine connected specialization has the stated hypotheses and conclusion. Tested the zero sheaf, a field as the zero-dimensional affine case, the empty scheme as excluded by connected-curve conventions, and degrees $q=0,1,2$.
- Step 1: checked [lem-sc-cohomological-dimension] for $q\geq3$, [lem-sc-regular-connected-integral] for the integral hypothesis, [lem-sc-generic-cohomology-comparison] for the degree-two isomorphism, and [lem-sc-affine-generic-second] for target vanishing. The torsion preservation under inverse image is stated explicitly as the local torsion check; no component decomposition is needed because connected regular curves are integral.
- New nodes: none; there are no new-node statements or Mathlib leaves to audit. Existing nodes were searched under `dag/nodes` before retaining these citations.
- Source and metadata: replaced the blueprint-only source pointer with the Stacks tag and label; completed the item as a split with its existing Lean theorem attachment and recorded blueprint realization.
- Citation repair: replaced the truncated generic-comparison citation with the complete verbatim statement required by the delivery checker.
- Edge cases and Lean attachment: the comparator theorem has the equivalent bound $2\leq q$; its body is sorry-free, while its dependency chain remains marked `rests_on_sorry`, so it is attached rather than declared closed.
