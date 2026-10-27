# CategoryTheory.Triangulated.TStructure.texact_system_triangle_coherence

## Reason

The proof constructs full triangle comparisons using the proved spectral-object API and
uses the existing cohomology-pasting declarations. It does not use the upstream Homology
module. Remove that unused public import. No declaration signature, definition, attribute,
or visibility changes. This is an import change in a Sheaf module; no adopted source
module is edited.

## Old

```lean
public import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import Mathlib.Order.Directed
```

## New

```lean
public import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
public import Mathlib.Order.Directed
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
```

The new private proof import exposes bodies of canonical cutoff maps only inside this
file. No new import is exported.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Triangulated.TExactSystemTriangleCoherence | H1 | Both statements preserved exactly; both proofs completed. |

`tools/downstream.py` reports zero downstream modules. A search of Lean source imports
also finds no direct importer. The declaration-use query lists only the item itself.
Parents that still cite the DAG node retain its unchanged statements and attachment.
No consumer adaptation is necessary, and no target statement or definition changes.

## Status

landed 20261024T185910-L-3755926 2026-10-24 (merge of deliver/H1/Sheaf.CategoryTheory.Triangulated.TExactSystemTriangleCoherence)
