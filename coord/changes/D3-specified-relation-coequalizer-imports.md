# CategoryTheory.specified_sheafified_relation_coequalizer

## Reason

The proof uses the presheaf coequalizer and the supplied bijection hη. It does not
use the covering-presieve site construction or any global sheafification API.
Remove these unused public imports and the redundant direct HasLimits import.
The theorem signature and specifiedRelationQuotientMap definition are unchanged.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
```

## New

```lean
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
```

## Users

`tools/downstream.py` reports zero downstream modules. A search of direct import
lines also finds none. Each declaration is referenced only within this module.
Thus no current importer needs adaptation or a separate compile. Planned DAG
parents continue to have exactly the same theorem and quotient-map interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SpecifiedSheafifiedRelationCoequalizer | D3 | Proved; unused imports removed; declarations unchanged. |

## Status

landed 20261026T091356-L-3336989 2026-10-26 (merge of deliver/D3/Sheaf.CategoryTheory.SpecifiedSheafifiedRelationCoequalizer)
