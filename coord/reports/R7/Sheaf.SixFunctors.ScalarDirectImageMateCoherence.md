## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.scalarDirectImageMateCoherence`
with its statement and both canonical definitions unchanged. Naturality is the
naturality of the constructed natural transformation. Mathlib's
`unit_mateEquiv` and `mateEquiv_counit` prove the adjunction identities.

For geometric composition, invert `ScalarSixPullbackData.composition`, paste
using `mateEquiv_hcomp`, change adjunctions using the two conjugation/pasting
identities, and cancel the inverse direct-image compositors. For scalar
composition, invert `ScalarSixPullbackData.tower`, apply `mateEquiv_vcomp`, and
transport along the actual tensor-tower isomorphisms. Two fully proved private
helpers package these categorical calculations; their proofs reuse the existing
private calculations in `Sheaf.Paper.PbcScalarExtension` without importing that
unrelated theorem module. A local heartbeat budget permits normalization of
the large derived-category expressions within the unchanged wall-time limit.
The only added import is a private proof import of
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`, for its proved
whiskering identity. No new public declarations, axioms, definitions or hypotheses.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.CondensedRing.scalarDirectImageMateCoherence`
(node `lem-sfb-scalar-direct-image-mate-coherence`).

Added 0 holes; 0 holes remain in the item. Both private helpers are completely
proved. This is a proof from the existing pullback data and their recorded
coherences, not a decomposition into new unproved statements. The existing
`scalarSixPullback` dependency is retained.

## No longer needed

No nodes or modules pruned. The proof follows the stated node plan and keeps
all its declared dependencies. No unused proof imports remain. Existing public
imports are retained as the module's published interface.

## Where the brief, the DAG or earlier work was wrong

None. The geometric helper first produces the equation with inverse conjugate
compositors; cancellation is necessary to put it into the statement's displayed
orientation. No statement repair, consumer adaptation or new node is needed.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
