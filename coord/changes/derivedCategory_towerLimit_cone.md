# derivedCategory_towerLimit_cone

## Reason

The repository already landed the upstream repair removing derived-category,
exactness, enough-injectives, and K-injectivity hypotheses. This follow-up repair
removes the remaining unused `Abelian` assumption; the second reader also removed
the first worker's unnecessary `Preadditive` assumption. The Mathlib construction only
needs zero morphisms to form cochain complexes, countable products
to provide the two required products, and equalizers for the equalizer construction.

## Old

```lean
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [Abelian A] [HasCountableProducts A] :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c)
```

## New

```lean
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [HasZeroMorphisms A]
    [HasCountableProducts A] [HasEqualizers A] :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone | P2 | Reviewed generalization; no target statement or definition changes. |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitTower | unclaimed | Existing Abelian assumptions synthesize the generalized assumptions; no source change required. |

The read-only downstream check finds 1566 transitive importers and exactly these
two textual users (including the theorem itself). The only direct importer is
DerivedLimitTower, whose unchanged proof compiles against the new signature. All
transitive statements retain their text and definitions. The cone node realizes no
unit statement or step, and its sole DAG citer remains valid. No target meaning
review is reopened.

## Status

landed 20261013T211110-L-394062 2026-10-13 (merge of deliver/P2/Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone)
