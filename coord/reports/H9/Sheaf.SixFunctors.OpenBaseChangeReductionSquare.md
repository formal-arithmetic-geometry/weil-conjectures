## What changed

Replaced the proof of
`WeilConjectures.OpenInterchangeReduction.openBaseChangeReductionSquare` with the
open-adjunction mate calculation, followed by the existing completion-transport
argument. The theorem's signature and public imports are unchanged. Added proof-only
imports of `TensorAdjunctionReductionSquares` (including its private ordinary-word
comparison and completion-cancellation helpers) and `CanonicalOpenReductionIsIso`.
All new helpers are private and proved. No other existing module was changed.
The complete proof compiled in 13.9 seconds; debugging options were then removed.
Local irreducibility attributes and a parameterized mate bridge keep equality
transports from expanding the underlying derived constructions.

The calculation pastes the two canonical pullback-compositor comparisons around the
scheme square, then transposes through the two specified open adjunctions. Both beta
maps retain their independently prescribed transpose normalizations. Naturality
inserts the child coefficient morphism; cancellation of the beta isomorphisms gives
the forward ordinary square. The existing completion helper gives the claimed
square on the original short-word admissible domain. This argument applies to the
empty open and zero input as well: no nonempty or nonzero cancellation is used.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.OpenInterchangeReduction.openBaseChangeReductionSquare`
(node `lem-sf-open-base-change-reduction-square`). Added zero holes and split off
zero statements. No `sorry` remains in the delivered module.

The proof uses existing declared dependencies, including
`canonicalReductionPullComposition`; their proof obligations remain with their
existing nodes. This report counts this module's one hole, not those dependencies.

## No longer needed

No original import was removed. No library module is withdrawn or claimed globally
unreachable. The old direct proof dependency `lem-sf-open-tensor-normalization` is
not separately applied: the beta transpose equations are already fields of the
published `OpenComparisons` and `RingedOpenComparisons` operation data. Its module
remains in the unchanged public import closure.

The proof does not need a separate preservation theorem for the longer intermediate
words in the adjunct expansion, or invertibility of the inner word's coefficient
map. It uses canonical pullback composition on arbitrary ordinary objects and
naturality in that child map. The original support/Tor/origin hypotheses remain
unchanged and are used by completion cancellation.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The existing DAG's phrase that every additional adjunct
vertex retains the same fixed windows is unnecessary here; the ordinary mate
calculation has no amplitude hypotheses. Only the endpoint completion transport
uses the stipulated windows. Updated the item's proof and proof dependencies to
record this route. The unit's coefficient-compatibility route is retained.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
