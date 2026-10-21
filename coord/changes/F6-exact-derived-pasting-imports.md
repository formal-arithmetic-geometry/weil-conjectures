# CategoryTheory.ExactDerivedPasting

## Reason

Remove the redundant public import of ExactDerivedComposition from
Sheaf.CategoryTheory.ExactDerivedTransformationPasting. The prescribed compositor is already
exported by the retained source ExactFunctor import. The proof uses its proved component
normalization, together with the cochain identity formula from ExactRestrictionComposition.
No declaration signature or definition changes.

## Old

```lean
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Sheaf.CategoryTheory.ExactDerivedComposition
import Mathlib.CategoryTheory.Localization.Predicate
```

## New

```lean
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ExactDerivedTransformationPasting | F6 | Redundant public import removed; private proof import added. |

The read-only downstream check found zero Lean modules downstream of the item and zero
consumers of existsUnique_mapDerivedCategoryCompIso through it. No consumer adaptations
are needed. DAG parents and the item itself are retained; this is no withdrawal.

## Status

landed 20261021T111111-L-4107956 2026-10-21 (merge of deliver/F6/Sheaf.CategoryTheory.ExactDerivedTransformationPasting)
