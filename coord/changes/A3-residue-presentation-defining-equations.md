# Canonical residue tensor presentation and its normalization equations

## Reason

Unfolding concrete sheaf-module derived functors repeatedly made the core exceed
60 seconds. Keep the canonical single comparison, braiding and balanced counit
as named data. Prove their defining equations once in their construction modules.
The names contain the original explicit constructions, with no choice of an
arbitrary witness and no unproved data. The paper tensor presentation retains its
named reduction/restriction functor and its actual balanced counit.

## Old

```lean
@[irreducible] noncomputable def derivedTensorSingleIso (B : C) :
    (tensorLeft B).leftDerivedFunctor ≅
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj B) := by
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)
  let eB : (DerivedCategory.singleFunctor C 0).obj B ≅ DerivedCategory.Qh.obj P :=
    (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _
  exact Functor.leftDerivedNatIso (tensorLeft B).leftDerivedFunctor
      (tensorLeft (DerivedCategory.Qh.obj P)) (tensorLeft B).leftDerivedFunctorCounit
      (DerivedCategory.tensorLeftQhObjCounit P) (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.isoWhiskerRight (homotopyTensorSingleIso B).symm DerivedCategory.Qh) ≪≫
    (curriedTensor (DerivedCategory C)).mapIso eB.symm
```

```lean
@[irreducible] noncomputable def derivedTensorPresentationIso (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B) := by
  let : BraidedCategory (DerivedCategory C) := DerivedMonoidal.braidedCategory
    (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
  exact Functor.leftDerivedUnique (tensorLeft B).leftDerivedFunctor H ε
      (tensorLeft B).leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (.up ℤ)) ≪≫
    derivedTensorSingleIso B ≪≫ BraidedCategory.tensorLeftIsoTensorRight _
```

```lean
@[irreducible] noncomputable def residueExchangeTensorIso (T : Scheme.{u}) :
    residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T ≅
      tensorRight (residueExchangeCoefficient ℓ E T) := by
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.residueDerivedTensorIso (coefficientMap (integralReductionMap ℓ E) T)
```

## New

```lean
@[irreducible] noncomputable def homotopySingleComparisonIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj B)) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _
```

```lean
@[irreducible] noncomputable def derivedTensorSingleIso (B : C) :
    (tensorLeft B).leftDerivedFunctor ≅
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj B) := by
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)
  let eB : (DerivedCategory.singleFunctor C 0).obj B ≅ DerivedCategory.Qh.obj P :=
    homotopySingleComparisonIso B
  exact Functor.leftDerivedNatIso (tensorLeft B).leftDerivedFunctor
      (tensorLeft (DerivedCategory.Qh.obj P)) (tensorLeft B).leftDerivedFunctorCounit
      (DerivedCategory.tensorLeftQhObjCounit P) (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.isoWhiskerRight (homotopyTensorSingleIso B).symm DerivedCategory.Qh) ≪≫
    (curriedTensor (DerivedCategory C)).mapIso eB.symm
```

```lean
@[instance_reducible] noncomputable def derivedTensorPresentationBraiding :
    BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))
```

```lean
@[irreducible] noncomputable def derivedTensorPresentationIso (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B) := by
  let : BraidedCategory (DerivedCategory C) := derivedTensorPresentationBraiding
  exact Functor.leftDerivedUnique (tensorLeft B).leftDerivedFunctor H ε
      (tensorLeft B).leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (.up ℤ)) ≪≫
    derivedTensorSingleIso B ≪≫ BraidedCategory.tensorLeftIsoTensorRight _
```

```lean
@[irreducible] noncomputable def residueExchangeTensorCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T) ⟶
      (tensorLeft ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
        (Mod.regular (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))).mapHomotopyCategory
            (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) T)
```

```lean
theorem residueExchangeTensorCounit_isLeftDerivedFunctor (T : Scheme.{u}) :
    (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T).IsLeftDerivedFunctor
      (residueExchangeTensorCounit ℓ E T) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  unfold residueExchangeTensorCounit residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
    (coefficientMap (integralReductionMap ℓ E) T)
```

```lean
@[irreducible] noncomputable def residueExchangeTensorIso (T : Scheme.{u}) :
    letI : MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
      CategoryTheory.tensorPresentationMonoidal
    residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T ≅
      tensorRight (residueExchangeCoefficient ℓ E T) := by
  letI : MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
    CategoryTheory.tensorPresentationMonoidal
  have := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E T
  exact derivedTensorPresentationIso _ _ (residueExchangeTensorCounit ℓ E T)
```

The proved `derivedTensorPresentationIso_fac` is the defining counit equation,
obtained from left-derived uniqueness and the defining transformation equation.
The reducible `tensorPresentationMonoidal` abbreviation names the existing generic
monoidal data. The explicit local instance in the paper is the same structure.
The ordinary and derived coefficient pullback definitions are unchanged;
`residueRestrictedRegularPullIso_def` and
`residueExchangeCoefficientPullIso_counit` prove their existing equations. Their
module publicly imports the model and ordinary tensor-square modules used by
these signatures. All new equations are fully proved.

## Users

The table contains every direct use reported by `tools/downstream.py --uses` for
`derivedTensorSingleIso`, `residueExchangeTensorIso`, and the tensor coefficient
comparison. The core's equivalent named-counit let body is recorded separately. No
Challenge declaration changes. Since a canonical construction used below the
targets is re-expressed, independent statement review of affected targets must
reopen; the intended comparison is still normalized by exactly the same counit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Canonical comparisons and named balanced counit; data constructed explicitly. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Shared braiding and coefficient comparison; same tensor maps. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Proved defining equation and coefficient-counit equation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitCore | A3 | Uses the proved generic normalization and the same actual constructors. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Same core statement and canonical maps. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Consumer check of the same canonical tensor presentation/model. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | B3 | Consumer check; no signature or visibility change allowed. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Consumer check of the same canonical tensor presentation. |
| Sheaf.Paper.IntegralResidueTensorRouteDescent | A3 | Consumer check: its sorry statement mentions residueExchangeTensorIso; the type is reducibly the same; compiles unchanged. |
| Sheaf.Paper.IntegralResidueTensorRouteKFlat | C2 | Consumer check: its sorry statement mentions residueExchangeTensorIso; the type is reducibly the same; compiles unchanged. |

## Status

landed 20261017T213021-L-1678945 2026-10-17 (merge of deliver/A3/Sheaf.Paper.IntegralResidueTensorPullCounitCore)
