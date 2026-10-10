# Worker report: `lem-weil-pbc-zero-dimensional-cohomology`

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-zero-dimensional-cohomology.json`: repaired the imported split, added the missing abelian-sheaf statement dependency, recorded the three required Mathlib searches, and retained two complete proof steps.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-geometric-point-coproduct-cohomology.json`: new unsplit finite-coproduct statement, with no Mathlib match.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, the blueprint tag, and the notions `zero-dimensional`, `etale cohomology`, `Spec k`, and `geometric stalk`. No declaration states the item exactly. The nearest declaration is `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_topologicalKrullDim_le_zero` in `AlgebraicGeometry/Curve/Reductions.lean:123-142`, but it is a different field-extension statement and its body is `sorry`.

## WANTED:

None. The cited Stacks etale-cohomology source and its labels are identified in the repository's obtained Stacks corpus metadata.

## What was wrong and what changed

The imported first paragraph cited only the curve-setting definition while using finite/discrete dimension-zero geometry, residue fields, reduction invariance, and a finite coproduct decomposition. It also cited no node for the stalk comparison in the second paragraph. The revised step 1 applies the residue-field leaf to `C_red` itself, uses the reduction universal-homeomorphism and finite-discrete-affine nodes, and writes the induced coproduct isomorphism explicitly. Step 2 applies the finite geometric-point coproduct statement, invokes universal-homeomorphism invariance, and uses the existing inverse-image-stalk-germ tool to identify `(i^{-1}F)_{c-bar}` with `F_{c-bar}`.

The source checked was Stacks Etale Cohomology, Proposition 03SI (`proposition-topological-invariance`), Theorem 03QT (`theorem-equivalence-sheaves-point`), Lemma 03QU (`lemma-compare-cohomology-point`), Section 03QQ (`section-cohomology-point`), and the first paragraph of Lemma 0A5B (`etale-cohomology-lemma-constant-smooth-statements`). The item statement agrees with the source: finite product of geometric stalks in degree zero and vanishing in positive degree. The finite/discrete and residue-field hypotheses are checked before reducing; the empty scheme is covered by the empty finite coproduct.

`tools/review_split.py lem-weil-pbc-zero-dimensional-cohomology` reports only the route warning that `lem-weil-pbc-reduction-universal-homeomorphism` is an unsplit generic fact from unit `sk-thm-p1`, while this item is in `sk-prop-cd`. This is the canonical reduction tool required by the blueprint's first paragraph; per delivery-errors C8 it should be recorded by L in `tool_uses` at merge. No other review error remains.

## Review by G1

I read the item's blueprint node and the unit route in `dag/units/sk-prop-cd.json`, then checked the item against the Stacks Etale Cohomology discussion of cohomology of a point (Lemmas 03QQ, 03QT, 03QU), topological invariance (Proposition 03SI), and the first paragraph of Lemma 0A5B. The item statement agrees with that source: for a separated finite-type dimension-zero scheme over algebraically closed `k`, the point set is finite, degree zero is the finite product of geometric stalks, and positive degrees vanish. The empty scheme is included by the empty finite coproduct.

For step 1, I opened each cited node and verified that it states the fact used: finite type plus dimension zero gives an Artinian finite/discrete space; closed-point residue fields equal `k`; reduction is a universal homeomorphism with reduced source; finite discrete schemes are affine; and the family coproduct has open-and-closed summands. The ring argument used in the step was tested on `Spec k` and on a finite product `k × k`; in each case the reduced one-prime component is a field and the coproduct description is exact. No step is marked elementary because each uses one of these nontrivial cited statements.

For step 2, I checked that the finite-coproduct node states positive-degree vanishing and finite-product assembly, while the universal-homeomorphism node supplies the cohomology identification. The existing `lem-weil-pbc-inverse-image-stalk-germ` node supplies the canonical stalk comparison and is declared as a generic C8 tool because this unit has no replacement for it. Its hypotheses apply to the reduction morphism and chosen geometric point. The finite-coproduct node is strictly smaller than the item and has complete hypotheses, source labels, and three-way Mathlib searches; no duplicate node was found by searching the full DAG and blueprint. `tools/check_dag.py` reports no cycles.

## What I could not finish

No Lean code is written at stage 1, and no unresolved source request or attachment remains. The unnecessary geometric-point node from the prior delivery was deleted.

