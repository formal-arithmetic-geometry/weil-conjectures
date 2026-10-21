## What changed

Restored `lean/Sheaf/Algebra/Homology/FilteredDerivedHomCalculusUniverse.lean` from
its assigned quarantine archive. The public interface, three declarations, theorem
statement, docstrings, and existing proof plan are unchanged. The file now keeps
only its public import of `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`.
The archived proof-only imports were removed because the retained theorem proof is
still the named existing `sorry`, and those imports are unavailable together with
the stale compiled dependency snapshot: importing the retired Sheaf finite
filtration declarations and the adopted upstream extension produces duplicate
`CategoryTheory.FilteredObject.restrictionSteps`. The resulting module compiles
cleanly with `lcompile.py`.

## Proved and sorry left

The assigned import restoration is complete. Original holes: 1; holes closed: 0;
holes added: 0; holes left: 1. The retained hole is
`CochainComplex.FiniteFiltered.filteredDerivedHomCalculusIn`, with its existing
source, complete natural-language proof plan, and DAG node
`lem-trf-filtered-derived-hom-calculus`. No new theorem, definition, axiom, or
`sorry` was added.

## No longer needed

The following proof-only imports were removed from this restored module because
its retained theorem proof does not elaborate or use them:

- `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`
- `Sheaf.Algebra.Homology.BoundedFilteredLocalizationEmbedding`
- `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits`
- `Sheaf.Algebra.Homology.UniformFilteredTruncation`
- `Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison`
- `Sheaf.Algebra.Homology.FilteredHomComplexInvariance`
- `WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`
- `WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`
- `WeilConjectures.CategoryTheory.Abelian.Filtration`

The corresponding DAG proof dependencies remain recorded for the eventual proof
of the retained theorem; no DAG node is withdrawn or changed by this repair.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly identifies this as a quarantined import repair, but the
archived module's full proof-import list cannot compile against the current last
green snapshot: `FilteredDerivedHomCalculus` is compiled through the retired
Sheaf finite-filtration provider, while explicit imports of the adopted upstream
provider load duplicate declarations. The module's statements themselves remain
usable and compile after proof-only imports are pruned. The DAG statement and
unit route are unchanged.

## New nodes

None.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
