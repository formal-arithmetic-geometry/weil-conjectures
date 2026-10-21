## What changed

Restored `Sheaf.Paper.IntegralResidueExchangeAlgebra` from its explicitly recorded
quarantine source after the cluster restore. Preserved the public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_exchange_square`, its full
signature, public import, two private helpers and existing DAG attachment. The final
proof uses the current pointwise `Adjunction.coefficient_exchange_of_counit_at`, with
the ambient exchange counit identities, actual push mate identities and pull cube at
the integral direct image of the given object. All four declared proof dependencies
are used. Updated the node's proof description and proof origin to record this.

Change record: `coord/changes/V1-integral-residue-exchange-algebra-restoration.md`.
The module compiles cleanly through `lcompile.py` (8.2 seconds for the revised proof;
13.7 seconds in the consumer check). The original archived direct consumer also compiles
(44.8 seconds), with only its four pre-existing line-length warnings. It is not delivered.
The assigned repair restores a missing public theorem; it is not a no-op or rebase.

## Proved and sorry left

The restored theorem `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_exchange_square`
is completely proved, as are private helpers `pull_transport` and `pull_square`.
Its node is `lem-weil-pbc-integral-residue-exchange-algebra`.
The archived item already had zero holes: 0 of 0 holes closed, 0 holes added,
0 split off, and 0 remaining locally. An explicit `#print axioms` of the restored
theorem reports `propext`, `Classical.choice`, `Quot.sound` and the existing transitive
`sorryAx` from the imported foundations. The restored result is proved from the existing
declarations, not claimed axiom-closed. Separate axiom probes show that
`coefficient_exchange_of_counit_at`, `composition_square_aux` and the ambient exchange
counit use only the three permitted axioms, whereas the existing push counit,
`residueExchangeUpperStarComp` and `residueExchangeAdjunction` already carry `sorryAx`.
This delivery reports restoration rather than net
sorry reduction. No new statements or definitions are introduced.

## No longer needed

None. Both imports remain needed: `BoundedExchangeAmbient` supplies the public
statement and ambient exchange counit; `CoefficientExchange` supplies composition
cancellation and the coefficient-exchange calculation. The universal wrapper
`coefficient_exchange_of_counit` is no longer called; its pointwise theorem in the
same module is used, so neither its module nor its DAG node can be pruned.
The quarantined parent `IntegralResidueExchange` still imports this module and
cites its theorem, and its node retains this proof dependency.

## Where the brief, the DAG or earlier work was wrong

The assignment is a quarantine-restoration repair with zero archived holes, not an
unfinished proof. The live absence was caused by the merge queue cluster restore
recorded in `coord/rework.tsv`; it does not authorize withdrawing the mathematics.
The old proof-origin note about a remaining coefficient-comparison theorem was stale
for this module; the replacement describes its fully implemented argument. The
statement, dependency list and unit route are unchanged. Library and Mathlib searches
found the generic mate tools already used; no replacement specialized theorem was found.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
