## What changed

Retire the assigned duplicate `Sheaf.CategoryTheory.FilteredStableSubquotient`
in favor of the existing proved upstream module. Its public theorem signature,
private helper, and full proof agree verbatim with the upstream declaration.
Reattach `lem-sp-filtered-stable-subquotient-at-bounds` to the upstream theorem,
keeping its statement, proof route, dependencies, and every parent edge.
There are no current direct importers to adapt. No upstream file changes.

Change record: `coord/changes/M3-retire-filtered-stable-subquotient.md`.

## Proved and sorry left

The assigned module starts with 0 sorries. Holes closed: 0. Holes added: 0.
No split-off theorems and no remaining sorry in the delivery.
`CategoryTheory.DecreasingFiltration.stableSubquotient_at_bounds` retains its
complete upstream proof with exactly the original statement. An explicit
server-compiled example checks that signature, and `#print axioms` checks the
upstream theorem. The original Sheaf module also compiled without warnings.

## No longer needed

Prune `Sheaf.CategoryTheory.FilteredStableSubquotient` using `deleted.txt`.
Its imports of `WeilConjectures.CategoryTheory.FilteredCohomologyImage`,
`WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation`,
`WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation`, and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` disappear with the
duplicate module. These upstream modules and the corresponding mathematical
nodes remain needed by the preserved upstream proof; none is withdrawn.
The DAG node itself remains, with its existing proof and parent dependencies.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof task, whereas the queue lists retirement
and the assigned source already has zero holes. The old DIFFERENT twin
inventory predates the unification of the dependent filtration and presentation
providers. The current signatures and full proofs match verbatim. The listed
former Sheaf consumer has already been replaced by its upstream module, which
imports the upstream theorem. No mathematical statement or unit route changes.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
