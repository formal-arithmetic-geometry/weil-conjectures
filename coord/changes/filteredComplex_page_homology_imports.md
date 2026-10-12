# CategoryTheory.filteredComplex_page_homology

## Reason

Remove the redundant public import of Mathlib.Algebra.Homology.ShortComplex.Abelian
from Sheaf.CategoryTheory.FilteredComplexPageHomology. Its declarations concern the
proof, and are already publicly available through the retained dependency chain:
FilteredComplexPageDifferential -> FilteredComplexBoundariesLECycles ->
FilteredComplexSubquotients -> HomologicalComplexAbelian -> ShortComplex.ExactFunctor
-> ShortComplex.Abelian. This removes no visible declaration in the actual public
import closure and changes no existing statement, definition or target meaning.
The preflight nevertheless requires a change record for a removed public import.

## Old

```lean
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles
```

## New

```lean
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Mathlib.CategoryTheory.Abelian.Exact
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredComplexSuccessorBoundariesImage
```

## Users

Ran tools/downstream.py Sheaf.CategoryTheory.FilteredComplexPageHomology --direct
--uses filteredComplex_page_homology. It lists one direct importer and two modules
mentioning the declaration including the item itself. The direct importer imports
the item privately, so its public signatures never expose this import path. A scratch
copy of its unchanged source compiled against the revised compiled item and the two
new modules with lcompile.py, with no errors or warnings. No forced adaptation is
needed. All 1150 transitive downstream modules retain the same statements and
available declarations: the retained public chain exposes the removed import's
entire contents, and the only direct importer itself compiles unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredComplexPageHomology | H2 | Existing signature unchanged; redundant public import removed. |
| Sheaf.CategoryTheory.FilteredComplexPositivePages | unclaimed | Unchanged source compiles; no declaration or statement changes. |

## Status

landed 20261012T194117-L-457028 2026-10-12 (merge of deliver/H2/Sheaf.CategoryTheory.FilteredComplexPageHomology)
