# Support model comparison factoring

## Reason

The expanded model comparison formulas repeatedly trigger conversion through derived functor and cone definitions. Restoring the expanded formulas exceeded the 60-second file gate. The generic exact and right-derived comparison definitions retain precisely the same compositions and specified natural isomorphisms. Their specialization is definitionally equal to the old bodies. No object is chosen from mere existence.

The unclaimed `Sheaf.AlgebraicGeometry.SupportTriangleConstruction` also factors the identical cone formula through the generic `supportSequenceTriangle`. The new definition has no choices or postponed proof.

## Old

```lean
noncomputable def supportShriekModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj
        (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K).obj :=
  letI := supportModelKInjective Λ I hI
  ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorObjQIso I).symm ≪≫
    (finiteClosedUpperShriek Λ s j).rightDerivedFunctor.mapIso eB ≪≫
    ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlusCompatibility.app K).symm

noncomputable def supportFirstModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportedSectionsComplex Λ s j hPair I) ≅
      ((supportClosedDerivedPlus Λ s j hPair).obj
        ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).obj :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  ((lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryFactors.app
    (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory.mapIso
      (supportShriekModelComparison Λ s j I hI K eB) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlusCompatibility.app
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).symm

noncomputable def supportThirdModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportCComplex Λ j I) ≅
      ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).obj :=
  letI := supportOpenModelKInjective Λ j I hI
  ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorObjQIso
    (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)).symm ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.mapIso
      (((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryFactors.app I).symm ≪≫
        (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.mapIso eB ≪≫
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlusCompatibility.app
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).symm
```

Original cone formula:

```lean
noncomputable def supportModelTriangle
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I))) :
    Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  letI := hq
  Triangle.mk (DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).f)
    (DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).g)
    (inv (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)) ≫
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.triangle (supportModelSequence Λ s j hPair I).f).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (supportModelSequence Λ s j hPair I).X₁)
```

## New

```lean
noncomputable def supportShriekModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj
        (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K).obj :=
  letI := supportModelKInjective Λ I hI
  (finiteClosedUpperShriek Λ s j).supportRightModelComparison I K eB

noncomputable def supportFirstModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportedSectionsComplex Λ s j hPair I) ≅
      ((supportClosedDerivedPlus Λ s j hPair).obj
        ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).obj :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).supportExactModelComparison
    (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (.up ℤ)).obj I)
    ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)
    (supportShriekModelComparison Λ s j I hI K eB)

noncomputable def supportThirdModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportCComplex Λ j I) ≅
      ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).obj :=
  letI := supportOpenModelKInjective Λ j I hI
  (lowerStar (ModuleCat.{u + 1} Λ) j).supportRightModelComparison
    (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex (.up ℤ)).obj I)
    ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)
    ((upperStar (ModuleCat.{u + 1} Λ) j).supportExactModelComparison I K eB)
```

Factored cone formula:

```lean
noncomputable def supportModelTriangle
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I))) :
    Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  supportSequenceTriangle (supportModelSequence Λ s j hPair I) hq
```

The two generic model definitions are `CategoryTheory.Functor.supportExactModelComparison` and `CategoryTheory.Functor.supportRightModelComparison`, attached to the existing localization-triangle node. Signatures and visibility of all existing declarations stay identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | A8 | Three bodies factored; all five holes proved. |
| Sheaf.AlgebraicGeometry.SupportTriangleConstruction | unclaimed | Formula factored through the explicit generic constructor; same signature and value. |
| Sheaf.AlgebraicGeometry.SupportTriangleCompatibility | unclaimed | Uses supportModelTriangle; unchanged and compiled as consumer. |

`tools/downstream.py --uses` found no other module mentioning any of these three comparison declarations. There are 178 transitive importers; their statements see unchanged signatures and definitionally equal data. No consumer is adapted. The construction module is unclaimed (no claim file); its definition is adapted under the unclaimed-module rule. Target statements and their mathematical meaning are unchanged.

## Status

landed 20261019T231034-L-541681 2026-10-19 (merge of deliver/A8/Sheaf.AlgebraicGeometry.SupportLocalizationTriangle)

Validation: construction and localization compile; SupportTriangleCompatibility and RetractedSupportLocalizationComparison compile unchanged. ClosedSupportExceptionalComparison times out both against the overlay and against the unchanged baseline (scratchpad/consumer-baseline-closed.log), so there is no attributable new failure and it is not adapted.
