## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingModule_isZero_of_open_closed` in
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`, without changing its signature.
The proved private helper `inverseImage_isZero_of_pullback` uses the existing scalar
restriction equivalence and tensor-extension adjunction from `ProEtaleOperations`.
Uniqueness of left adjoints identifies extension along the coefficient isomorphism
with the inverse equivalence, which reflects vanishing.

The main proof applies `proEtale_ringed_open_closed` to `ProEt.mk j`, transports open
vanishing through its displayed equivalence, and equips extension by zero and direct
image with their provided adjunctions. They therefore preserve zero objects. Exactness
of the displayed counit/unit sequence and Mathlib's
`ShortComplex.Exact.isZero_of_both_isZero` prove the claim.

The proof-only `import all Sheaf.AlgebraicGeometry.ProEtaleOperations` makes its
already proved private scalar-transport constructions available, as existing library
proofs do. All existing public imports and declarations retain their visibility.
No definitions, statements, consumers, or DAG route changed. No split-offs or new nodes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtaleRingModule_isZero_of_open_closed`
(node `lem-exc-open-closed-detection`). Added 0 holes. No `sorry` remains in the item
or its new private helper. This is a proof from existing declarations, not a decomposition.

Server single-file compilation passed without warnings. `#print axioms` reports
`propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`: the existing
imported dependency theory remains unfinished. This delivery closes the assigned
local hole; it does not claim that the transitive proof is axiom-clean. The argument covers empty
open or closed complements and arbitrary commutative ring-sheaf coefficients; no
nonempty, finite, constant-coefficient, or qcqs hypothesis was added.

## No longer needed

Removed proof-only import
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`: the normalized
pullback/direct-image adjunction is unnecessary for coefficient transport. The
existing tensor-extension adjunction in `ProEtaleOperations` suffices. This does not
claim that the canonical-adjunction module is globally unreachable.

All three declared proof dependencies remain used:
`def-weil-pbc-proetale-operations`, `lem-weil-pbc-proetale-ringed-open-closed`, and
`def-weil-pbc-exact-sequence`. No DAG dependency is pruned. The localization theorem's
filtered-colimit assertion and the qcqs assumptions in that assertion are unused,
as the original plan specifies.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. `ProEt.mk j` requires explicit local instances for
`IsOpenImmersion V.hom` and `QuasiCompact V.hom` during elaboration; both are precisely
the existing hypotheses on `j`. The existing proved scalar-transport constructions
avoid repeating the tensor-balancing calculation. The current blueprint statement
and Stacks Project `proetale.tex`, `lemma-ses-associated-to-open` (Tag 09AH), agree
with this route. Searches with leanfinder, loogle, grep, and local source searches
found the exact Mathlib zero-end-term lemma but no replacement for localization.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
