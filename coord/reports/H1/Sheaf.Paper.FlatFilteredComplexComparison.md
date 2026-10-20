## What changed

Restored `lean/Sheaf/Paper/FlatFilteredComplexComparison.lean` from the archive named by
its current `coord/rework.tsv` row. This is the assigned quarantine restoration, not a
new proof delivery. The archive and its mathematical content are preserved verbatim.
The restored file compiles through `lcompile.py` in 1.5 seconds.

The recorded failure was the duplicate `CategoryTheory.DecreasingFiltration.IsExhaustive`
introduced by combining `Sheaf.CategoryTheory.Filtration` with upstream
`WeilConjectures.CategoryTheory.CanonicalFiltration`. The current dependencies have
already been migrated: `FlatFilteredScalarExtension` and `FilteredPageTwoModel` publicly
import upstream `FilteredComplexSubquotients`, which uses `CanonicalFiltration`, and
`FiniteFiltrationInduction` also uses `CanonicalFiltration`.
`Sheaf.CategoryTheory.Filtration` is now an empty withdrawn module. Consequently the
archived item can be restored without modifying any dependency or declaration.

Consumer checking: `tools/downstream.py` reports the item as unknown because its active
source is quarantined. A search of both `lean/` and `quarantine/` for the module and
declaration names finds only the archived declaration itself; there is no consumer to adapt.

No existing definition, statement, public import, or DAG field is changed. The change
record is `coord/changes/H1-flat-filtered-complex-comparison-restoration.md`.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. No decomposition.

The original named theorem `CategoryTheory.flatFilteredComplex_comparison` remains
`sorry`, with its original source and complete proof plan in its docstring and its
original node `lem-pc-flat-filtered-complex-comparison`. The repair restores this
statement to the Lean library; it does not claim to prove it.

## No longer needed

None. No imports, declarations, nodes, or modules are withdrawn or pruned. In particular,
the mathematical dependency on this node in `lem-pc-flat-base-change-cohom` remains.
All original proof-dependency imports and the node attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The quarantine diagnostic describes an older dependency graph. On the current graph,
the archived item itself compiles unchanged because the filtration API migration has
already been completed in its dependencies. Its absence from `lean/` is still a real
restoration issue; it is not evidence that its statement has been withdrawn.

The natural-language node, unit route, Lean signature, and original proof plan are
unchanged. Searches with `msearch.py` (LeanFinder, Loogle, and grep) and local searches
found no existing flat filtered-complex comparison theorem replacing this statement.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
