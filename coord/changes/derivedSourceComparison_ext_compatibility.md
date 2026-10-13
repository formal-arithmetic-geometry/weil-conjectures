# CategoryTheory.derivedSourceComparison_ext_compatibility

## Reason
Relocate the compatibility declaration and its unchanged sourceExtMap dependency into a dedicated module, and correct its DAG statement and proof description.

## Old
Absent from the current repository baseline. In the earlier returned worker delivery, this declaration was in `Sheaf.CategoryTheory.DerivedSourceComparisonInjective`, with the same signature and (for the map) defining expression.

## New
Relocated to `Sheaf.CategoryTheory.DerivedSourceComparisonExtCompatibility`. Exact delivered declaration (signature; proof now complete):

```lean
theorem derivedSourceComparison_ext_compatibility
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L) (Y : C) (q : ℕ)
    (x y : (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦(q : ℤ)⟧)
    (hxy : ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map x =
      ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map y) :
    sourceExtMap V L B a Y q
      (Abelian.Ext.homEquiv.symm (ShiftedHom.map x (DerivedCategory.Plus.ι (C := C)))) =
    sourceExtMap V L B a Y q
      (Abelian.Ext.homEquiv.symm (ShiftedHom.map y (DerivedCategory.Plus.ι (C := C))))
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedSourceComparisonInjective | B2 | Imports the relocated module and uses both declarations. |

## Status
landed 20261013T172650-L-2097784 2026-10-13 (merge of deliver/B2/Sheaf.CategoryTheory.DerivedSourceComparisonInjective)
