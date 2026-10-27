## What changed

Replaced the proof hole in `Module.orthogonal_split_idempotents_small_module` with the
four-step argument already recorded in its DAG node. Split operators give fixed vectors
for the projections; applying a projection and its retraction to each finite relation
forces every coefficient to vanish. Mathlib's `linearIndependent_le_span''` gives an
injection into every spanning set after lifting the index and module to a common
universe. The injection transfers countability and proves the final vanishing clause.
Added only the private proof import `Mathlib.Algebra.Module.ULift`.
The declaration's signature, visibility, docstrings and existing public imports are unchanged.

## Proved and sorry left

Closed the one hole in `Module.orthogonal_split_idempotents_small_module`
(node `lem-sfb-orthogonal-split-idempotents-small-module`). No holes remain in the item;
no holes were added and no statements were split off.

## No longer needed

None. All three declared dependencies remain used: `def-weil-field` supplies the
field cancellation, `lem-sfb-independent-family-spanning-cardinality` is the Mathlib
cardinality theorem, and `def-sfb-countable-set` supplies countability under injection.
No imports, nodes or modules are removed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The common-universe lifts mentioned in the plan are
necessary because the original index and module universes are independent; the proof
transports both the independent family and the spanning set through a linear equivalence.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
