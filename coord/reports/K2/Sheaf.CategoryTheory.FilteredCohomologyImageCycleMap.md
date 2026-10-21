## What changed

Retired the listed duplicate module
`Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap` and reattached node
`new-cohomology-image-cycle-map` to the existing upstream declaration
`CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map` in
`WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap`. The sole direct
consumer, `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized`, now imports
that upstream module. Its theorem statements and proof are unchanged. The
retired path is recorded in `deleted.txt`.

Change record: `coord/changes/retire-filtered-cohomology-image-cycle-map-K2.md`.

Both the upstream theorem and the migrated consumer compile with `lcompile.py`;
compiling the sandbox in import order succeeds. A scratch `#print axioms` check
on the upstream theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No `sorry` remains in the replacement provider or the adapted consumer. This is
a retirement of an already proved duplicate, not a decomposition.

## No longer needed

Pruned the duplicate Sheaf module and all of its duplicate imports. The Sheaf
proof-helper imports are replaced by the canonical upstream module's imports.
No mathematical node, unit route, or proof dependency is pruned. The indirect
consumers remain unchanged and continue to resolve the same theorem through
`FilteredCohomologyImageNormalized`.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a module, but the current queue explicitly
classifies this item as `retire` in `coord/queue.tsv` and
`coord/retire-items.tsv`. The module already had a complete proof from earlier
landings. The adopted source now contains an equivalent complete upstream twin,
so retaining the Sheaf copy would preserve an unnecessary duplicate. The node's
old attachment was stale after the canonical homology-filtration migration.

The upstream theorem was checked directly, and its declaration signature agrees
with the node statement clause by clause. The unit record
`sk-prop-av-pqf-finite` has no realized statement or proof step involving this
auxiliary node, so the retirement does not bypass a unit route. Repository search,
LeanFinder, Loogle, and grep searches found no shorter Mathlib theorem that would
replace the upstream result.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
