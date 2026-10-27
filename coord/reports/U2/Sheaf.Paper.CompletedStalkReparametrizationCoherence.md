## What changed

Proved `pointUnits` from finite-field characteristic and the prime-to-characteristic hypothesis. Proved `sectionsRoos_existsUnique` using the already proved point-sections product/Roos comparison and the uniqueness of the additive scalar Roos map. A proved private helper converts the degreewise coordinate equations to that uniqueness property. Added proof-only imports of `Sheaf.Paper.PointQuotientAugmentationDiagram` and `Sheaf.Paper.IntegralOperationsScalarComparisons`. The DAG proof and dependency list now record these local obligations and their proofs. Re-expressed the still-open section normalization using explicit underlying linear-map functions and equivalent heterogeneous equality, to avoid expensive carrier conversion. See `coord/changes/U2-completed-stalk-section-normalization.md`.

## Proved and sorry left

Closed `WeilConjectures.CompletedStalk.pointUnits` and `WeilConjectures.CompletedStalk.sectionsRoos_existsUnique` (2 of 8 original holes); added no holes.

Six existing holes remain: `WeilConjectures.CompletedStalk.towerReparam_existsUnique`, `WeilConjectures.CompletedStalk.reparam_existsUnique`, `WeilConjectures.CompletedStalk.sectionRestriction_existsUnique`, `WeilConjectures.CompletedStalk.rationalComparison_existsUnique`, `WeilConjectures.CompletedStalk.rationalReparam_existsUnique`, and `WeilConjectures.CompletedStalk.coherence`. All belong to `lem-trf-completed-stalk-reparametrization-coherence`.

## No longer needed

None. No imports, DAG nodes, or modules were pruned. The unfinished assembly still needs the original dependencies.

## Where the brief, the DAG or earlier work was wrong

The original section-normalization presentation caused a full-file compile timeout. Its equivalent HEq presentation compiles without changing the mathematical assertion; this hole is explicitly not counted as proved. The existing generic Roos comparison supplies the local sections/Roos obligation directly; no new cone construction or split lemma is needed.

## New nodes

None.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
