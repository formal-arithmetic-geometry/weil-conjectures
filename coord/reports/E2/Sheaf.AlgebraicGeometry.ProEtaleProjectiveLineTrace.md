## What changed

Restored `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace` from its quarantine
archive and repaired the compile-time defect. `SpP1DiagonalIntegralsAt` now names
the product scheme and its diagonal using local let-bindings. This keeps Ext-smallness
instance checking over local endpoints instead of repeatedly expanding the concrete
projective-line product. Unfolding the two let-bindings recovers the original predicate.

The profiled revised module compiled in 31.6 seconds, compared with 75–91 seconds
for preceding versions. Profiling options are removed for delivery.

All public signatures, imports, canonical maps, existing theorem proofs and DAG proof
dependencies are preserved. The item's existing node attachment is retained, with an
appended explanatory note. Change record:
`coord/changes/E2-proetale-projective-line-trace-sharing.md`.

## Proved and sorry left

This is a performance repair of an already proved module: zero holes before,
zero holes after, zero holes closed, zero holes added, zero split off.
The preserved proved public theorems are `exists_spP1BaseTraceConditions`,
`spP1DiagonalIntegrals_of_twisted`, and `proEtale_projectiveLine_trace`.
No declaration in the delivery has a `sorry`. Imported unfinished theorems remain
ordinary declared dependencies; no target-level axiom-freedom claim is made.

## No longer needed

None. No import, node, module, declaration, attachment or dependency is withdrawn.
The module is still needed by its DAG parents even though the current Lean tree
has no direct importers. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned source was absent from `lean/` because it was quarantined, not because
it was withdrawn. Its `coord/rework.tsv` row records a 66.7-second compile.
Profiling the archived source reproduced the failure and located the cost in
kernel checking of `SpP1DiagonalIntegralsAt`, its generated Ext-smallness proofs,
and `diagonalIntegralsAt_generic`. Tactics themselves were fast. Explicit local
HasExt instances alone did not solve it; sharing the constructed geometric endpoints
addresses the repeated type conversion without changing mathematics.

No statement dispute or mathematical change was needed. Searches used LeanFinder,
Loogle, the logged grep service, and local searches in both library roots; the
existing canonical-arrow and biproduct proof route is retained.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
