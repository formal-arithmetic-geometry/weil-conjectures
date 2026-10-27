## What changed

Replaced the hole in `WeilConjectures.sfNormalizedInputTransition` with explicit
transport from `sfDirectImageInputTransition_adjacent`. Proved private helpers
identify the adjacent ordinary restriction functors, identify their canonical
derived compositors, and transport the scalar-adjunction transpose across that
identification. Local exactness instances supply the direct quotient restriction.
The item module's existing imports and public statement are unchanged.
Updated the item's DAG proof and proof dependencies to match this route.
The completed proof compiled in 16.9 seconds; the delivery tool reruns validation
and the axiom probe after the final local-binding style cleanup.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.sfNormalizedInputTransition`
(node `lem-sf-normalized-input-transition`). Holes added: zero. Split off: zero.
No `sorry` remains in the delivered module. The proof uses the existing theorem
`WeilConjectures.sfDirectImageInputTransition_adjacent`, whose existing downstream
obligation `WeilConjectures.compactSupportInput_completed_tower` remains outside
this delivery. This is a proof from the recorded dependencies, not a claim that
the entire reduction tower is axiom-free already.

## No longer needed

No imports removed and no modules withdrawn. The node no longer needs a separate
K-flat representative calculation or a direct proof dependency on
`lem-pc-kflat-resolution`: the existing adjacent-transition theorem already
provides that input. The former direct proof dependencies
`def-weil-integral-reduction-tower`,
`lem-weil-derived-scalar-extension-restriction-adjunction`, and
`lem-sf-compact-support-proper-image-tower` remain in the statement's interface
where relevant; their general theorems are not invoked anew. They are not claimed
to be globally unused or pruned modules. The sole remaining theorem dependency
is `lem-sf-direct-image-input-transition-adjacent`.

## Where the brief, the DAG or earlier work was wrong

The planned K-flat computation need not be repeated here. The remaining gap is
only transport between two presentations of the same adjacent restriction and
its compositor. Directly applying the adjacent theorem makes Lean unfold large
coefficient constructions and reaches the default heartbeat bound; explicit
comparison lemmas avoid that conversion. No statement or definition repair,
consumer adaptation, or unit-route change is needed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
