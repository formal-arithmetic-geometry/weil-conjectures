## What changed

Proved `AlgebraicGeometry.Scheme.pbc_actual_completed_reduction_reconstruction` in
`Sheaf.Paper.ActualCompletedReductionReconstruction`, keeping its statement unchanged.
The proof first obtains reconstruction for the derived strict quotient tower from
`completedKoszulQuotientComparison` and `completedRlim_roos`. It then identifies the
strict transitions with the displayed adjunction transitions using the normalized
scalar units and evaluation counits, and transports the product vertices of the
Roos triangle. All auxiliary calculations are proved private helpers in the item.
The node's proof and proof dependencies record this route.
Preflight requested a record for added proof-scoped commands; it is
`coord/changes/p8-actual-completed-reconstruction-proof-scope.md`.
The public interface is unchanged and no consumers require adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.pbc_actual_completed_reduction_reconstruction`
(`lem-weil-pbc-actual-completed-reduction-reconstruction`).
Zero holes remain in the item. Zero holes and zero split-off obligations are added.
The full module compiled cleanly through `lcompile.py` in 16.6 seconds.

## No longer needed

The direct planned dependency
`lem-weil-pbc-completed-koszul-reduction-roos-triangle`
(`Sheaf.Paper.CompletedKoszulReductionRoosTriangle`) is unnecessary for this proof:
the existing actual-coefficient Koszul quotient comparison and strict derived-limit
Roos triangle already give its required conclusion. No withdrawal is proposed.
The direct planned dependency `lem-pur-derived-change-of-rings` is also unnecessary:
the required scalar adjunction and exact restriction calculations are supplied by
`BoundedConstructibleTower` and its existing interfaces. Its module is retained.
The original two public imports are preserved. Redundant direct private imports of
`IntrinsicCompletion` and `CompletedRlimFunctor` were removed because the quotient
comparison publicly provides their interfaces. No existing modules are deleted.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The planned constant-presentation
Roos construction can be shortened using the already proved actual-coefficient
Koszul quotient comparison. The coefficient presentation still matters when
transporting the given completeness certificate. The strict tower evaluation maps
must be checked against the canonical adjunction-based quotient transitions; level
isomorphisms alone are insufficient. The proof supplies that check on K-flat
representatives and extends it by resolutions. The unit `sk-rem-rest` has no realized
statement or proof-step entry bypassed by this change.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
