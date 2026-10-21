## What changed

Restored the quarantined module `Sheaf.Algebra.Homology.DerivedCanonicalFiltration` from its
complete proof archive. Updated the retired `FilteredObject.HomPreservingSteps` references to
the current official `FilteredObject.Hom` API. The existing theorem proof and all private helpers
remain fully proved; the interface migration is recorded in
`coord/changes/G4-DerivedCanonicalFiltration-hom-api.md`. the node's Lean attachment now records the current signature.

## Proved and sorry left

Closed 1 of 1 original holes: `DerivedCategory.exists_derivedCanonicalFiltration`.
No `sorry` remains in the item, no holes were added, and no definitions contain `sorry`.

## No longer needed

No proof dependency or import was removed. The quarantined proof already uses the current
bounded-roof, canonical-truncation, finite-filtered-homotopy, and filtered-localization modules.
No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined source and its node attachment still named the retired
`FilteredObject.HomPreservingSteps` structure. The adopted upstream filtration API provides
`FilteredObject.Hom` with the same `hom` and preservation fields, so the source was restored by
that representation migration. The mathematical theorem statement is unchanged.

## New nodes

None.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
