## What changed
`AlgebraicGeometry.genus_jacobian_invariant` now has a complete assembling proof, with its original signature unchanged. It derives geometric integrality from geometric connectedness and smoothness, uses `baseChange_curve` for the connected base-change curve, rewrites both genera as arithmetic genera, and applies `arithmeticGenus_pullback`. A proved private helper repackages `exists_jacobian` into `IsJacobian`, checking the dimension and multiplicative representation fields.

The final compatibility square is isolated in the new module `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible`. This is strictly the last part of the argument: it assumes geometric integrality and the connected base-change curve and proves neither genus invariance nor the existence of Jacobians. The main proof establishes these hypotheses and all other conclusions independently. The existing node's proof and dependencies now follow this route.

## Proved and sorry left
- `AlgebraicGeometry.genus_jacobian_invariant`: its one original sorry is replaced by a complete reduction.
- The private helper `exists_jacobian_of_connected` is proved.
- `AlgebraicGeometry.jacobian_compatibility`, in the new module, remains sorry (node `lem-sc-jacobian-base-change-compatible`). Its docstring contains the source and complete natural-language construction via the Picard presheaf comparison, sheafification units, the slice adjunction and Yoneda.

Local compilation of both modules in import order passed without warnings. The remaining theorem's identity-extension and genus-zero cases are consistent: the chosen identifications determine the comparison isomorphism; no positivity of the genus is required.

## No longer needed
Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.Variety`
- `WeilConjectures.AlgebraicGeometry.DensePoints`

The parent proof no longer directly needs nodes `lem-sc-proper-dim-one-projective`, `lem-weil-pbc-finite-type-over-noetherian`, `def-pc-curve`, `def-pc-smooth-projective-curve`, `def-pc-separably-closed`, `lem-pc-rational-points-dense`, and `prop-pc-xk-integral`. Geometric integrality follows from the existing geometric-connectedness and smoothness lemmas without choosing a rational point or first constructing a projective embedding. `def-pc-base-change` and `cor-pd-pic0-base-change` are now dependencies of the isolated compatibility node instead of direct dependencies of the parent. `lem-sc-flat-base-change-coherent` is used through `lem-pc-genus-base-change` rather than directly. These are local pruning claims; the report does not assert these nodes are globally unreachable.

## Where the brief, the DAG or earlier work was wrong
The recorded `nonempty_picardFunctorDegree_iso_of_isPullback` gives existence of a Picard comparison, but its signature does not include the compatibility equation on line-bundle classes. Its implementation constructs the canonical comparison, and its construction plus sheafification naturality are the route needed for the isolated theorem. An arbitrary isomorphism of Picard functors would not suffice for that equation.

The explicit projectivity/rational-point route in the old step 1 is unnecessary for the existing `exists_jacobian` signature. No target, definition, existing theorem signature, or unit route was changed.

## New nodes
`lem-sc-jacobian-base-change-compatible`, in `dag/nodes/sec-curve-estimates/lem-sc-jacobian-base-change-compatible.json`, records the compatibility clause with its geometric hypotheses already established. Its Lean module is `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible`; its proof follows step 3 of the parent blueprint. LeanSearch returned an Internal Server Error and is recorded as unavailable; LeanFinder, Loogle and grep searches ran. Loogle found the generic representing-object uniqueness theorem, which alone does not give the Picard comparison equation. No change record is needed: existing statements and public imports are unchanged.

## Second reading by U2
I compared the delivered `GenusInvariant.lean` declarations byte for byte with the repository version and found the target signature unchanged; only proof text and proof-only imports changed. Both delivered modules compile in import order with no errors or warnings. The main theorem has no remaining sorry; the isolated compatibility theorem is the named split-off theorem with a matching node and complete source/docstring proof plan. Its hypotheses and conclusion match the parent compatibility clause, including the specified pullback and classifying-map equation. The route preserves the unit steps: geometric properties and connected base change, arithmetic-genus base change, Jacobian existence, then compatibility. I found no hollow definitions, forbidden declarations, or unnecessary public imports beyond the recorded split-off module.

I added this second-reading record only; no Lean statements or proofs were changed after the initial compilation.
