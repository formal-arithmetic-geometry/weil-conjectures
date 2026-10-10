# Stage 1 report: lem-pc-twist

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-twist.json`: statement node split into the three imported proof steps; no new nodes.
- `dag/units/sk-thm-picard-twist.json`: realized statement and proof step recorded.
- `citations.json`: 20 step-to-node verbatim citations.

## Attachments

`AlgebraicGeometry.Scheme.exists_isInvertible_twist` belongs to `lem-pc-twist` as the corresponding Lean declaration, but is not closed because its transitive proof rests on sorry.

`AlgebraicGeometry.Scheme.finrankH_zero_tensorObj_pullback_toModules_ker_add_one` is the Lean implementation of the point-removal argument in Step 3 of `lem-pc-twist`; it is partial and not a separate DAG node.

`AlgebraicGeometry.Scheme.exists_isInvertible_twist_of_finrankH_zero_eq` is the Lean implementation of the descending-induction argument in Step 3 of `lem-pc-twist`; it is partial and not a separate DAG node.

The remaining open declarations in the slopmaster2 audit are already represented by existing nodes: `subsingleton_H_of_lt` by `lem-pc-vanishing-above-dim`; finite locally free `dual`, `tensorObj`, and their dual-tensor isomorphism by `lem-sc-degree-2g1-very-ample`; higher-direct-image comparison and finiteness declarations by `lem-pc-euler-characteristic-well-defined` / `lem-pc-coherent-hi`; `nonempty_H_pullback_linearEquiv` by `lem-sc-flat-base-change-coherent`; and `exists_isIso_pushforwardHomObjComparison_unit` by `lem-sc-finite-duality`.

## WANTED

None. The proof source is represented by the blueprint and the cited Stacks tags are available locally.

## Review by E1

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-twist/lem-pc-twist.md`, the unit route `dag/units/sk-thm-picard-twist.json`, and the Lean source `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean` at the three tagged declarations (lines 1794--1988 in the slopmaster2 checkout). The theorem statement agrees with the blueprint: a separably closed field, smooth projective curve, arbitrary field extension, and an invertible sheaf on the base change, with dimensions one and zero after a descended twist.

For Step 1 I read the statements of `lem-pc-very-ample-ample`, `lem-pc-dim-base-change`, `lem-pc-closed-imm-base-change`, `lem-pc-ample-positive-degree`, and `lem-pc-degree-base-change`. They supply respectively the ample pullback, dimension-one base change, stability of the closed immersion (with the flat ideal identification used later), positivity of degree, and degree preservation under field extension. The hypotheses are met because the source gives a smooth projective curve and a field extension.

For Step 2 I read `lem-pc-serre-vanishing`, `thm-picard-serre-a`, `lem-pc-degree-base-change`, `lem-pc-euler-additive`, `lem-pc-flat-base-change-cohom`, `prop-pc-xk-integral`, `lem-pc-vanishing-above-dim`, and `lem-pc-dim-base-change`. These say exactly the vanishing, global generation, degree and Euler-characteristic identities, flat cohomology base change, integral base change, and higher-cohomology vanishing used in the calculation of chi and the nonzero H0. The finite-dimensionality and genus hypotheses are inherited from the cited curve and cohomology nodes.

For Step 3 I read `lem-pc-rational-points-dense`, `def-pc-curve`, `prop-pc-xk-integral`, `cor-pc-dense-points-curves-sections`, `lem-sc-point-cartier`, `lem-pc-closed-imm-base-change`, and `def-sc-invertible-module`. They establish density of k-points after extension, integrality and dimension one, a point outside the zero locus, invertibility of the point ideal, its flat base change, and closure of invertible modules under tensor product. The exact sequence and long-exact-sequence dimension calculation are written out in the step itself; the induction decreases H0 by one while preserving H1=0.

I checked small cases: when the initial H0 dimension is one, Step 3 is empty; for the zero sheaf the hypotheses do not apply because the sheaf is invertible; on P1 the construction agrees with twisting by O(n) and removing rational points. I did not alter the imported statement or its route. The only correction was changing the imported status to `split`, filling `blueprint.same_as` with the empty search result, recording the unit realization, and documenting that the Lean theorem cannot be attached because of transitive sorry dependencies.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Second reading by E1

- Item statement: checked against the blueprint node and the Stacks references Tag 0B9Y (Picard Schemes, Lemma 44.6.5) and Tag 0B8Z (Varieties, Lemma 33.44.16); the separably closed field, smooth projective curve, field extension, invertible sheaf, and two cohomology-dimension conclusions agree hypothesis by hypothesis.
- Step 1: checked against the statements of `lem-pc-very-ample-ample`, `lem-pc-dim-base-change`, `lem-pc-closed-imm-base-change`, `lem-pc-ample-positive-degree`, and `lem-pc-degree-base-change`; the pullback, dimension, ideal, positivity, and degree claims are supplied under the item's hypotheses.
- Step 2: checked against `lem-pc-serre-vanishing`, `thm-picard-serre-a`, `lem-pc-degree-base-change`, `lem-pc-euler-additive`, `lem-pc-flat-base-change-cohom`, `prop-pc-xk-integral`, `lem-pc-vanishing-above-dim`, and `lem-pc-dim-base-change`; the vanishing, generation, Euler-characteristic, base-change, integrality, and dimension claims match. The tensor-degree citation now quotes the tensor clause explicitly.
- Step 3: checked against `lem-pc-rational-points-dense`, `def-pc-curve`, `prop-pc-xk-integral`, `cor-pc-dense-points-curves-sections`, `lem-sc-point-cartier`, `lem-pc-closed-imm-base-change`, and `def-sc-invertible-module`; the point choice, Cartier ideal, exact sequence, one-dimensional fibre, induction, and descent are justified. The zero-sheaf case is excluded by invertibility; the $t=1$ case is immediate; on $\\mathbf P^1$ the construction is the usual subtraction of rational points.
- New nodes: none; therefore B1--B7 and duplicate/mathlib-leaf checks are vacuous. The item remains the sole split node and its `blueprint.same_as` search result is recorded as empty.
- Changes: corrected the Step 2 `lem-pc-degree-base-change` citation to quote the clause used for tensor-product degree additivity, and added this second-reading audit. No mathematical statement or proof step was changed.

