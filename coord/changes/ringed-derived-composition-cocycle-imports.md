# CategoryTheory.ringedDerivedComposition_cocycle

## Reason

Both this theorem and `CategoryTheory.ringedDerivedComposition_units` follow directly
from the assumed total-right-derived universal properties and comparison-unit equations.
Remove the unused resolution proof imports and the public composition-theorem import.
Import the Mathlib definitions used by the statements directly. The direct import of
`Mathlib.Algebra.Category.Grp.FilteredColimits` supplies the small-site sheafification
instances needed for the existing abelian module categories.

No declaration signature, universe parameter, visibility, definition, or target changes.
The only change visible to importers is the smaller public import closure.

## Old

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
```

## New

```lean
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.RingedDerivedCompositionCocycle
--uses ringedDerivedComposition_cocycle` reports zero downstream modules and only the
item itself as a declaration-name occurrence. A direct `rg` search for the module and
both theorem names in `lean/Sheaf` and `lean/WeilConjectures` likewise finds no external
Lean consumer. Consequently no consumer adaptation or additional compile is needed.
DAG parents with unfinished proofs retain the same interfaces and normalization equations.
The item remains present and proved; it is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedDerivedCompositionCocycle | P4 | Both theorem signatures unchanged; public import closure reduced; proofs completed. |

## Status

landed 20261021T111412-L-108279 2026-10-21 (merge of deliver/P4/Sheaf.CategoryTheory.RingedDerivedCompositionCocycle)
