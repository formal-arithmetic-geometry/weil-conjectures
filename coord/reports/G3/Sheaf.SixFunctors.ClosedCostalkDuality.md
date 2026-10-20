## What changed

`ClosedCostalkDuality.lean` now proves both exceptional restriction theorems by applying
uniqueness of right adjoints to the common-left-adjunction decompositions. The categorical
uniqueness bridge is proved in the new module `Sheaf.SixFunctors.CommonLeftAdjunctionIso`.
The two common-left-adjunction constructions are retained as named intermediate statements
with their own DAG nodes and are the only deferred parts of the original six-step argument.

## Proved and sorry left

Closed: `nonempty_iso_of_common_left_adjunctions`,
`exceptionalRestrictionVerdierDuality_etale`, and
`exceptionalRestrictionVerdierDuality`.

Sorry left (split off):
`exceptionalRestrictionVerdierDuality_etale_common_left_adjunction` and
`exceptionalRestrictionVerdierDuality_proetale_common_left_adjunction`.
These are strictly smaller intermediate results asserting the two adjunctions needed before
right-adjoint uniqueness; each has a DAG node.

## No longer needed

The final Lean route uses the generic adjunction uniqueness theorem and the two new common-left
adjunction statements. The original geometric-support and tensor-Hom proof dependencies remain
recorded on the parent DAG node because they are the stated proof obligations of those
intermediate results; no existing library module was removed.

## Where the brief, the DAG or earlier work was wrong

The original module contained no usable Lean-level construction for its long six-step Hom
calculation. The DAG described that calculation in prose but did not expose the common left
adjunction as a separately usable declaration. This delivery makes that missing intermediate
interface explicit and leaves its construction for the next worker.

## New nodes

`lem-weil-closed-costalk-etale-common-left-adjunction` records the etale common-left-adjunction
intermediate theorem.

`lem-weil-closed-costalk-proetale-common-left-adjunction` records the pro-etale analogue.

`lem-weil-common-left-adjunctions-iso` records and proves the generic categorical uniqueness
bridge. No change record is needed because no existing declaration signature or definition was
changed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
