## What changed

Proved `AlgebraicGeometry.Scheme.coefCompactSupportReductionAdjoint` in
`Sheaf.Paper.CompactSupportReductionAdjoint`, preserving its statement and all public
imports. Added the private proof import
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` to transfer intrinsic bounded
constructibility from W along beta inverse. Applied the existing
`finiteCompactSupportScalarComparison` at levels m+1 and n+1 for invertibility of the
specified comparison. The adjunction Hom-equivalence unit formula, naturality of the
specified restriction comparison at beta, associativity and functoriality prove the
transition identity. Functorial preservation of isomorphisms proves the final clause.
Updated the item's node to record the existing isomorphism-closure dependency.

## Proved and sorry left

Closed the single existing hole in
`AlgebraicGeometry.Scheme.coefCompactSupportReductionAdjoint`
(node `lem-coef-compact-support-reduction-adjoint`). Holes closed: 1; holes added: 0;
split off: 0. No `sorry` remains in the item or is added elsewhere. This is a proof
from the existing library declarations; their underlying dependency proofs are
unchanged.

## No longer needed

None. All existing planned dependencies remain in use. No modules or nodes are
withdrawn, and no public imports are removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The DAG's elementary constructibility
transport step is implemented with the existing isomorphism-closure clause of
`proEtale_bounded_constructible_isTriangulated`, now explicitly recorded as a proof
dependency. No statement, definition, coefficient map or compactification changes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
