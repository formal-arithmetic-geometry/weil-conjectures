## What changed

Replaced the remaining proof hole in `pbcIsoAmbientPullback_preserves` by a real
conjunction proof. The three defining preservation clauses are now separate strict
intermediate theorems in the parent module, each documented with its transport
argument. The parent applies those component statements through the
normalized ordinary-derived comparison.

## Proved and sorry left

Closed the parent declaration `pbcIsoAmbientPullback_preserves` (1 hole). Added
three strictly smaller named statements whose proofs remain `sorry` for parallel
work:

- `pbcIsoAmbientPullback_preserves_intrinsic`
- `pbcIsoAmbientPullback_preserves_reductions`
- `pbcIsoAmbientPullback_preserves_origins`

Thus 1 hole was closed and 3 holes were split off.

## No longer needed

No imports were added. The original imports and proof dependencies remain used by the module; the component statements are local to the existing module
to keep its isolated compile within the required timeout.

## Where the brief, the DAG or earlier work was wrong

The earlier module left the entire three-clause preservation result as one opaque
hole, while the proof plan explicitly consists of three independent transport
clauses. The delivery records those clauses as separate DAG nodes so they can be
proved independently without weakening the parent statement.

## New nodes

- `lem-wf-pbc-automorphism-transport-intrinsic`
- `lem-wf-pbc-automorphism-transport-reductions`
- `lem-wf-pbc-automorphism-transport-origins`

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
