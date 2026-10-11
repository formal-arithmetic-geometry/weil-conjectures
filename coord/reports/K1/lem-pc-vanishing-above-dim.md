# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-vanishing-above-dim.json`: statement split; no new nodes; Mathlib searches found no matching theorem.
- `citations.json`: verbatim quotes for all cited proof steps.

## Attachments

`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le` was not attached: its proof depends on the sorried `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`.

## WANTED

None.

## Review by K1

I read the item's blueprint node and the Lean declaration in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean` (lines 316--327), plus the sorried dependency in `AlgebraicGeometry/Cohomology/EulerChar.lean` (lines 64--73). The Lean declaration has the right conclusion but is not a valid attachment because of that dependency. I also read the existing DAG statements `lem-weil-pbc-finite-type-over-noetherian`, `lem-pc-scheme-dimension-local-rings`, and `lem-sc-noetherian-cohomology-above-dimension`.

Step 1 uses the finite-type-over-Noetherian statement exactly: the curve definition supplies finite type over `Spec k`, and the field spectrum is Noetherian. Step 2 uses the dimension comparison exactly: `def-pc-dimension` gives local-ring dimension one, and the cited node identifies it with topological Krull dimension. Step 3 uses the existing cohomology-vanishing statement with the verified hypotheses from Steps 1--2 and `q >= 2`, so `1 < q`. The `citations.json` quotes are copied verbatim from those three node statements.

I removed the imported affine-cover proof because it introduced unsupported claims about Cartier divisors, affine complements, and Cech computation that were unnecessary and not all justified for an arbitrary base field. Small cases are consistent: for a one-dimensional curve the bound starts at degree two, while the general theorem also handles empty and zero-dimensional schemes.

## Second reading by K1

- Step 1 checked against Stacks Tag 01T6 (finite type over a Noetherian scheme) and the cited curve definitions; verdict: the smooth projective curve supplies finite type over the Noetherian field spectrum, so the Noetherian conclusion is valid.
- Step 2 checked against Stacks Tag 04MU (scheme dimension equals the supremum of local-ring dimensions) and the cited dimension definitions; verdict: the curve dimension hypothesis gives topological Krull dimension one, with nonemptiness supplied by integrality.
- Step 3 checked against Stacks Tag 02UZ (Noetherian cohomology vanishing above dimension) via the existing quasi-coherent specialization; verdict: for every integer q >= 2, one has topological dimension one < q and the cited vanishing applies.
- No new nodes are present; therefore B1-B7, duplicate-node search, and Mathlib-leaf classification require no node changes. The recorded Mathlib searches were checked as run searches, including the unavailable LeanSearch result.
- Edge cases checked: a one-point or zero-dimensional scheme has no cohomology in degrees >= 2, and the empty scheme is covered by the existing vanishing node; the stated curve is nonempty by integrality.
- Changes made in this second reading: none to the node or citations; appended this review record because the proof and citations were already correct.

