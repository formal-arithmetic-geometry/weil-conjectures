# derivedCategory_towerLimit_cone

## Reason

Upstream review #1424 identified that the former theorem carried derived-category,
exactness, enough-injectives, and K-injectivity hypotheses unused by its conclusion.
The delivered theorem retains `Abelian A` and `HasCountableProducts A`: countable
products lift to cochain complexes, and abelianness supplies their equalizers.
Mathlib's `hasLimit_of_equalizer_and_product` then constructs the required limit.
The final proof supplies `I.asFunctor` explicitly to `limit.cone` and `limit.isLimit`
instead of leaving these arguments as elaboration placeholders.

## Old

```lean
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c)
```

## New

```lean
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [Abelian A] [HasCountableProducts A] :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTower | unclaimed | Its existing Abelian/countable-products context supplies the delivered hypotheses; no caller statement change is needed. |

## Status

landed 20261013T222416-L-1227657 2026-10-13 (merge of deliver/T3/Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone)
