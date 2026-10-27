## What changed

Retired the duplicate module
`Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi` listed in
coord/retire-items.tsv, using deleted.txt. Reattached node
`sbc-lem-higher-image-colimit-comparison-epi` to the existing official module
`WeilConjectures.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi` and
recorded its exact signature. The official theorem has the same name and
conclusion, with the unused hK argument omitted; all other hypotheses and
universes agree. No source-library file or target statement is changed.

The mathematical parent is already the official
`WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineClassDescent`. It
imports the official epimorphy module and uses its hK-free signature. It needs
no adaptation. The dependency on epimorphy and the underlying continuity route
remain intact; this is duplicate retirement, not bypassing a unit step.

Change record: coord/changes/retire-higher-direct-image-colimit-comparison-epi-G4.md.

## Proved and sorry left

The item has zero direct holes before retirement and zero afterwards.
Holes closed: none (0 of 0). Holes added or split off: none (0).
No theorem with sorry is left or introduced by this delivery.

The retained `AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison`
(node `sbc-lem-higher-image-colimit-comparison-epi`) is the existing upstream
proof, not a new proof claimed by G4. Its existing raw affine representative
and local-surjectivity dependencies are preserved.

## No longer needed

The duplicate module
`Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi` is pruned.
Its public import of HigherDirectImageTransitions and private import of
HigherDirectImageRawAffineImageRep disappear with the duplicate file; the
official theorem continues to use these official modules. No mathematical DAG
node or proof dependency is pruned. No importers require edits, including
quarantined sources. The sole mathematical parent keeps the same dependency
node, now correctly attached to the official module it already imports.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an obligation with sorry. The current item is
instead a listed duplicate retirement and already has a complete proof. Its
DAG attachment still pointed to the Sheaf copy, while its parent had already
migrated to the official theorem. The retirement list marks the twins DIFFERENT
because the official signature omits hK. This difference is harmless here:
hK was explicitly unused in the old cancellation proof, and the official theorem
proves the old conclusion under fewer assumptions. No mathematical statement is
weakened, and no upstream declaration is removed or changed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
