## What changed

Restored `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` from the quarantine archive and
kept the previously delivered proof of `CochainComplex.kunnethConvolution_decreasing`. Replaced
its public import of the duplicate `Sheaf.CategoryTheory.FiniteFiltrationInduction` API with
`WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension`, which supplies the same
`FilteredObject` restriction and graded-map declarations without the current environment collision.
Change record: `coord/changes/M2-filtered-tensor-upstream-filtration.md`.
The restored module compiles with its quarantined importer `Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement`.

## Proved and sorry left

Closed `CochainComplex.kunnethConvolution_decreasing` (one sorry closed). The existing
`CochainComplex.filteredTensor_graded_comparison` remains sorry (one sorry left), as it is the
seven-step comparison theorem and was not replaced by a weaker statement. No new sorries were added.

## No longer needed

The duplicate `Sheaf.CategoryTheory.FiniteFiltrationInduction` import is no longer needed by this
module; the upstream `WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension` API is used
instead. No DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined file's original import order/API caused an environment declaration collision:
`CategoryTheory.DecreasingFiltration.IsExhaustive` was already present through the upstream
canonical-filtration API. Restoring the prior proof and using the upstream finite-filtration API
repairs the module on the current tree. The earlier delivery was also removed from `lean/` after
its base commit, so restoration from `quarantine/` was required.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
