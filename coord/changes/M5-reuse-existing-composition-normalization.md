# CategoryTheory.UnboundedSectionsLocalization.compIso_objQ

## Reason

The returned delivery duplicated this already proved private lemma. Make the existing
lemma public in its original unclaimed Sheaf module, delete the duplicate private proof,
and import and use it in module_derived_compositor_normalization. Its complete binders,
conclusion and proof remain unchanged. Its original use in unboundedSectionsLocalization
also remains unchanged. The Comp import becomes public because the newly public signature
mentions Functor.PreservesKInjectiveComplexes, which that module defines. The first compile
confirmed that retaining a private Comp import prevents elaboration of this signature.
No target, definition body, instance or existing public signature changes.

## Old

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

private lemma compIso_objQ
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Q.obj I) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((F ⋙ G).rightDerivedFunctorObjQIso I).hom
```

## New

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

lemma compIso_objQ
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Q.obj I) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((F ⋙ G).rightDerivedFunctorObjQIso I).hom
```

## Users

The original helper has only one existing user, in its own module; the item adds the
second use. All downstream modules reported by tools/downstream.py are listed below.
Making a fully qualified lemma visible and reexporting its existing signature dependency
preserves every previous declaration and data construction. No module needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | M5 | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion | T9 | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.ClosedTestDerivedExchangeModel | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.ClosedTestKInjectiveSectionModels | M8 | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | F8 | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.RootTowerCoordinateFace | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.TraceFormula.DerivedBasisLocalExtSheaf | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.TraceFormula.LciKoszulDualityData | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |
| Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison | unclaimed | Existing signatures, data and proofs unchanged; no consumer adaptation. |

## Status

landed 20261023T151855-L-418610 2026-10-23 (merge of deliver/M5/Sheaf.Paper.ModuleDerivedCompositorCoherence)
