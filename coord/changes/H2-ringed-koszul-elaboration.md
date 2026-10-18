# CategoryTheory.ringedKoszulTensor

## Reason

Keep the total tensor abstract during categorical compatibility proofs, to avoid
expanding its large construction. The local irreducibility attribute is restored
locally when constructing the tensor unit isomorphisms. It is not exported.
Two canonical local proposition-instance caches avoid repeated inference.
All existing signatures and definition bodies, including the derived-category
constructions, are preserved. No target statement or mathematical meaning changes.

## Old

```lean
def ringedKoszulTensor : ringedSiteComplex O ⥤ ringedSiteComplex O ⥤
    ringedSiteComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (CategoryTheory.MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
```

## New

```lean
def ringedKoszulTensor : ringedSiteComplex O ⥤ ringedSiteComplex O ⥤
    ringedSiteComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (CategoryTheory.MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

attribute [local irreducible] ringedKoszulTensor
```

The additional local instances `ringedKoszulHasSheafCompose` and
`ringedKoszulLimitPreservesZeroMorphisms` each prove an existing canonical
Mathlib proposition by `inferInstance`. They introduce no data choices or
assumptions. Scoped transparency settings enable matching of definitionally
equal concrete categories in the proofs. The tensor unit isomorphisms locally
restore semireducibility; downstream reducibility is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedKoszulSystem | H2 | Local elaboration controls and nine proofs. |

`tools/downstream.py --uses ringedKoszulTensor` reports only this module as a
direct user of the tensor declaration. The downstream modules
`Sheaf.CategoryTheory.RingedCechKoszulDualLimit` and
`Sheaf.CategoryTheory.RingedKoszulCompletionReflector` retain identical APIs and
need no forced adaptation. No other module is modified.

## Status

landed 20261018T071155-L-1668733 2026-10-18 (merge of deliver/H2/Sheaf.CategoryTheory.RingedKoszulSystem)
