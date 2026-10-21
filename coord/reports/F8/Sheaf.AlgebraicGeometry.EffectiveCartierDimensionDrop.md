## What changed

Filled the proof of
`AlgebraicGeometry.topologicalKrullDim_subscheme_of_isInvertible` in
`Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop`, preserving its signature,
docstring and imports. The proof follows all three steps of
`lem-sc-effective-cartier-dimension-drop` and Stacks Tag 0BEV
(`literature/stacks-project/varieties.tex`, `lemma-ample-positive`).

For each point of the divisor, invertibility supplies an affine open with a
nonzerodivisor generator. The point lifts to the corresponding member of
`J.subschemeCover`, so its quotient ring is nontrivial and the generator is a
nonunit. Integrality supplies the domain instance, and the source library's
`IsAffineOpen.algebra_finiteType_of_field` supplies finite type over the field.
The existing `effective_cartier_affine_dimension_drop` then gives the quotient
chart's dimension. The source library's `topologicalKrullDim_opens_eq` identifies
the ambient affine chart's dimension with `d`. Cancelling one in `WithBot ℕ∞`
gives `d - 1`, including the boundary case `d = 1`. Finally, the open-cover upper
bound and the subspace lower bound give equality for the divisor.

Searches through `msearch.py` (LeanFinder, Loogle and grep), together with direct
searches of both library roots, found no shorter scheme-level Cartier dimension
theorem. No new declarations, modules or nodes are needed. The final file compiled cleanly
through `lcompile.py` on the project server in 1.9 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.topologicalKrullDim_subscheme_of_isInvertible`
(node `lem-sc-effective-cartier-dimension-drop`).

No `sorry` remains in the item and no holes are added or split off. The proof
uses the existing declared affine dependency
`AlgebraicGeometry.effective_cartier_affine_dimension_drop`
(node `lem-sc-effective-cartier-affine-dimension-drop`), whose proof is still
`sorry` in the shared source; it is not changed or newly introduced here.

## No longer needed

None. Both existing proof imports are used, and all the node's planned proof
dependencies remain needed. No modules or nodes are withdrawn. The blueprint
unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The first two compile requests received no answer
from the busy compile server after 210 seconds each; both were retried according
to the brief. Once the server answered, two local elaboration errors were repaired
and the completed proof compiled cleanly.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
