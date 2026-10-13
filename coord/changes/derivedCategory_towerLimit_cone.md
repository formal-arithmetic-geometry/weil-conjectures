# derivedCategory_towerLimit_cone

## Reason

Repair upstream review #1424, queued in coord/repairs.txt. The theorem proves existence
of a limit of a tower of cochain complexes. Its derived-category, exactness,
enough-injectives and K-injectivity hypotheses do not enter the proof.
The corrected statement removes all five unused hypotheses and the unused universe w.
Countable products and abelianness remain: they supply the products and equalizers.

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

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone
--uses derivedCategory_towerLimit_cone` identifies exactly the two modules below
as textual users. Its 1537 transitive downstream modules have no other calls.
The sole direct importer is DerivedLimitTower, which already publicly imports all
three removed public dependencies independently. No downstream statement changes.
The cone node is not a unit realization. Its sole DAG citer remains valid because
all its original hypotheses still suffice for the generalized cone-existence theorem.
No target declaration or definition changes, so no target meaning review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone | Q4 | Hypotheses removed as requested; proof retained. |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTower | unclaimed | Forced one-line proof adaptation; signature and visibility unchanged. |

The forced adaptation changes line 50 only, from
`have hc' := (derivedCategory_towerLimit_cone A hP) hI I` to
`have hc' := (derivedCategory_towerLimit_cone A) I`.
The original fails against the changed dependency with:

```
Application type mismatch: The argument hP has type
HasCountableProducts (DerivedCategory A)
but is expected to have type CochainComplex (ℕᵒᵖ ⥤ A) ℤ
in the application derivedCategory_towerLimit_cone A hP
```

The adapted module compiles against the changed dependency. No other line of that
module changes. No additional claim is required under the forced-adaptation exception.

## Status

landed 20261013T201807-L-3976112 2026-10-13 (merge of deliver/Q4/Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone)
