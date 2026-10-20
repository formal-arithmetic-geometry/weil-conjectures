## What changed

Restored the quarantined module and reordered its public imports so that
`Sheaf.CategoryTheory.FiniteFiltrationInduction` is imported before
`WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`. This avoids the
stale environment collision on `CategoryTheory.DecreasingFiltration.IsExhaustive`
while preserving all declarations and signatures.

## Proved and sorry left

No theorem holes were closed in this repair. The existing holes remain:

- `CochainComplex.kunnethConvolution_decreasing` (blueprint:
  `lem-kun-filtered-tensor-graded-comparison`).
- `CochainComplex.filteredTensor_graded_comparison` (blueprint:
  `lem-kun-filtered-tensor-graded-comparison`).

## No longer needed

No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined source imported the two modules in an order that triggered an
environment declaration collision in the current compiler cache. Importing the
Sheaf finite-filtration API first makes the module compile cleanly.

## New nodes

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
