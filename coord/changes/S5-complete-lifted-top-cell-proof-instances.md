# CompleteLiftedTopCell proof-instance elaboration

## Reason

The original `letI` bindings inline their explicit instance values while elaborating the new proof. Replacing these bindings with `let` avoids repeated inlining; local priority for the canonical scalar-reduction derived-category instances additionally avoids repeatedly unfolding competing standard localizations. Both forms register the same instance value. Zeta reduction of the explicit local bindings gives definitionally equal definitions; no construction, signature, universe, visibility, or mathematical meaning changes.

The restriction exactness instances are propositions. The two changed `HasDerivedCategory.standard` bindings in `residueTorTest` carry localization data, so their equality is justified by their identical explicit values and zeta reduction, not by proof irrelevance. The two `EssentiallySmall` bindings and the `scalarReductionTargetDerived` binding in that definition remain unchanged.

The complete proof previously compiled without warnings in 53.8 seconds, and its exact delivery probe compiled in 58.1 seconds. This repair preserves the reviewed Lean proof and corrects the change record's explanation. A separate server-compiled check establishes equality of all four old and new definitions by `rfl`. The earlier landing failed because the reviewer override filename was the repository basename rather than the `.change.md` alias expected by the landing tool. The delivered record remains `coord/changes/S5-complete-lifted-top-cell-proof-instances.md`; a reviewer overriding it must name the fix `S5-complete-lifted-top-cell-proof-instances.change.md`.

## Old

```lean
def freeQuotient (r : ℕ) :
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ⟶
        (scalarReductionRestriction l E T 0).obj (residueFree l E T r) :=
  letI := scalarReductionRestrictionLimits l E T 0
  Limits.Pi.map (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0) ≫
    inv (piComparison (scalarReductionRestriction l E T 0)
      (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)))
```

```lean
def freeCellQuotient (r : ℕ) (b : ℤ) :
    DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b) ⟶
      (scalarReductionDerivedRestriction l E T 0).obj (residueCell l E T r b) :=
  letI := scalarReductionRestrictionLimits l E T 0
  letI := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.singleFunctor (scalarReductionSource l E T) b).map
      (freeQuotient l E T r) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategorySingleFunctor b).inv.app
      (residueFree l E T r)
```

```lean
def topReduction (M : DerivedCategory (scalarReductionSource l E T)) (b : ℤ) :
    (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).obj M ⟶
      (scalarReductionRestriction l E T 0).obj
        ((DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).obj
          ((scalarReductionDerivedExtension l E T 0).obj M)) :=
  letI := scalarReductionRestrictionLimits l E T 0
  letI := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).map
      (CompletedCoefficientFree.reductionMap l E T 0 M) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategoryHomologyFunctorIso b).inv.app
      ((scalarReductionDerivedExtension l E T 0).obj M)
```

```lean
def residueTorTest (M : DerivedCategory (scalarReductionSource l E T))
    (a b : ℤ) (V : T.ProEt) : Prop :=
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  letI : EssentiallySmall.{max u (t + 1)} (Over V) := essentiallySmallSelf _
  letI := scalarReductionTargetDerived.{t, u} l E T 0
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    ((integralCoefficientSheaf l E T 0).over V))
  letI := HasDerivedCategory.standard (ringedSiteModules.{max u (t + 1)}
    ((sheafCompose ((ProEt.topology T).over V)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((integralCoefficientCommRingSheaf l E T 0).over V)))
  HasRingedSiteTorAmplitudeOfUniverses.{t + 1, t, max u (t + 1)}
    ((integralCoefficientCommRingSheaf l E T 0).over V)
    ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
      (integralCoefficientSheaf l E T 0) V).obj
        ((scalarReductionDerivedExtension l E T 0).obj M)) a b
```

## New

```lean
def freeQuotient (r : ℕ) :
    (∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ⟶
        (scalarReductionRestriction l E T 0).obj (residueFree l E T r) :=
  let := scalarReductionRestrictionLimits l E T 0
  Limits.Pi.map (fun _ : Fin r ↦ CompletedCoefficientFree.quotientProjection l E T 0) ≫
    inv (piComparison (scalarReductionRestriction l E T 0)
      (fun _ : Fin r ↦ SheafOfModules.unit (integralCoefficientSheaf l E T 0)))
```

```lean
def freeCellQuotient (r : ℕ) (b : ℤ) :
    DerivedCategory.Q.obj (CompletedCoefficientFree.freeCell l E T r b) ⟶
      (scalarReductionDerivedRestriction l E T 0).obj (residueCell l E T r b) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.singleFunctor (scalarReductionSource l E T) b).map
      (freeQuotient l E T r) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategorySingleFunctor b).inv.app
      (residueFree l E T r)
```

```lean
def topReduction (M : DerivedCategory (scalarReductionSource l E T)) (b : ℤ) :
    (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).obj M ⟶
      (scalarReductionRestriction l E T 0).obj
        ((DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) b).obj
          ((scalarReductionDerivedExtension l E T 0).obj M)) :=
  let := scalarReductionRestrictionLimits l E T 0
  let := scalarReductionRestrictionColimits l E T 0
  (DerivedCategory.homologyFunctor (scalarReductionSource l E T) b).map
      (CompletedCoefficientFree.reductionMap l E T 0 M) ≫
    ((scalarReductionRestriction l E T 0).mapDerivedCategoryHomologyFunctorIso b).inv.app
      ((scalarReductionDerivedExtension l E T 0).obj M)
```

```lean
def residueTorTest (M : DerivedCategory (scalarReductionSource l E T))
    (a b : ℤ) (V : T.ProEt) : Prop :=
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  letI : EssentiallySmall.{max u (t + 1)} (Over V) := essentiallySmallSelf _
  letI := scalarReductionTargetDerived.{t, u} l E T 0
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    ((integralCoefficientSheaf l E T 0).over V))
  let := HasDerivedCategory.standard (ringedSiteModules.{max u (t + 1)}
    ((sheafCompose ((ProEt.topology T).over V)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((integralCoefficientCommRingSheaf l E T 0).over V)))
  HasRingedSiteTorAmplitudeOfUniverses.{t + 1, t, max u (t + 1)}
    ((integralCoefficientCommRingSheaf l E T 0).over V)
    ((ringedDerivedRestrictionGeneral.{t + 1, t, max u (t + 1), max u (t + 1)}
      (integralCoefficientSheaf l E T 0) V).obj
        ((scalarReductionDerivedExtension l E T 0).obj M)) a b

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CompleteLiftedTopCellTriangle | S5 | The only user of all four definitions; original theorem statement retained, complete proof compiles. |

`tools/downstream.py --uses` reports zero downstream modules for each of the four names. Repository searches agree. All existing signatures and their semantics stay identical, including target interpretations; there are no forced adaptations.

## Status

landed 20261024T191040-L-235563 2026-10-24 (merge of deliver/S5/Sheaf.SixFunctors.CompleteLiftedTopCellTriangle)
