# FiniteDiagonalReduction.closedSourceMap

## Reason

The unclaimed FiniteProductReductionComparisons exceeded 60 seconds during
consumer checking. Its profile assigned 40.4 seconds of kernel checking to
closedSourceMap and 20.5 seconds to its coefficient specialization.
The trace compares Etale.cartierAbelianPro with sheafIsAbelian and expands
derived-category localization structures. The scalar comparison modules use
Mathlib's canonical abelian structure. Prioritize that instance locally and
write the three canonical isomorphisms defining closedSingleIso at that
structure, avoiding the cached-instance conversion.

## Old

```lean
@[irreducible]
def closedSourceMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] [HasCompactification i]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} B) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B))
    (q : (proScalar φ Z).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N) :
    (proScalar φ T).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj M)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).obj N) :=
  (proScalar φ T).map (ProEtale.AffineZeroPurity.closedSingleIso A i M).inv ≫
    proCompactCoefficientMap φ i ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) i).map q ≫
    (ProEtale.AffineZeroPurity.closedSingleIso B i N).hom
```

## New

```lean
attribute [local instance 2000] CategoryTheory.sheafIsAbelian

@[irreducible]
def closedSourceMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] [HasCompactification i]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} B) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B))
    (q : (proScalar φ Z).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N) :
    (proScalar φ T).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj M)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).obj N) :=
  (proScalar φ T).map
      ((ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) i).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategorySingleFunctor 0).app M).inv ≫
    proCompactCoefficientMap φ i ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) i).map q ≫
    ((ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} B) i).app ((DerivedCategory.singleFunctor _ 0).obj N) ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} B) i).rightDerivedFunctorIsoMapDerivedCategory.app
        ((DerivedCategory.singleFunctor _ 0).obj N) ≪≫
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).mapDerivedCategorySingleFunctor 0).app N).hom
```

closedSingleIso has precisely this three-isomorphism composition as its body.
The component maps, order, chosen compactification and degree-zero comparisons
are unchanged. Every signature text, public import and global attribute is
preserved. The priority is local. No global instance, source-library file,
mathematical statement, target meaning or proof hole changes.

The repaired module and its unchanged direct consumer
FiniteDiagonalOrientationReduction compiled together through lcompile.py.
The unchanged test copy is not delivered.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same canonical data; align abelian structures locally. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same public signatures and canonical comparisons; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public signatures and canonical comparisons; no adaptation. |

## Status

landed 20261026T065516-L-3036452 2026-10-26 (merge of deliver/E3/Sheaf.Paper.AffineSpaceZeroSectionPurity)
