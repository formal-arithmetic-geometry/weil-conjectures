# CategoryTheory.Triangulated.TStructure.texact_truncation_triangle_comparison

## Reason

Use the already proved upstream comparison and boundary API directly. The theorem's exact
signature is unchanged. Its two original public imports contain no additional statement data
needed here. This delivery removes them and publicly imports the module defining IsTExact and
the canonical isomorphisms that occur in the statement. No source-library module is edited.

## Old

```lean
public import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
```

## New

```lean
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.TExactTruncationTriangleComparison
--uses texact_truncation_triangle_comparison` reports zero downstream modules. The only textual
use of the declaration is its own module. The unfinished DAG parent remains supported by the
unchanged theorem signature. No target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.TExactTruncationTriangleComparison | P3 | Proof completed; imports reduced to the statement API. |

## Status

landed 20261024T190526-L-4082038 2026-10-24 (merge of deliver/P3/Sheaf.CategoryTheory.Triangulated.TExactTruncationTriangleComparison)
