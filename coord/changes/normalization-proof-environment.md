# WeilConjectures.isomorphismDerivedPullbackComparisonNormalization

## Reason

Record the proof-environment commands conservatively classified as an interface
change by stage-3 preflight. The added reducibility attributes are local, and the
new options control elaboration of this proof. The new private constructions
comparisonFromModel and roosModel support the proof only. The existing public
imports, theorem signature and global instance-removal command are preserved.
The three new supporting modules remove the instance only within individual
declarations, using `attribute [-instance] ... in`.
No existing data definition or statement changes, and no consumer is adapted.

## Old

Original environment commands, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures
```

Original declaration signature, verbatim:

```lean
theorem isomorphismDerivedPullbackComparisonNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (hS : Nonempty (CoefficientDerivedSystemCoherence l E Y S))
    (N :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y))
    (hN : IsDerivedCompleteUnrestricted.{t, u} l E Y N) :
    ∃ θ : ∀ M :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y),
      (integralDerivedPullback l E g).obj M ≅
        (inverseImageIntegralDerived l E g).obj
          ((S.reduction ⋙ coefficientSequenceLimit l E Y).obj M),
      (∀ M :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y),
        inverseImagePullbackComparisonDerived l E g hX hY M ≫
            (θ M).hom =
          (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app M)) ∧
      (∀ (M M' :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y))
        (f : M ⟶ M'),
        (integralDerivedPullback l E g).map f ≫ (θ M').hom =
          (θ M).hom ≫
            (inverseImageIntegralDerived l E g).map
              ((S.reduction ⋙ coefficientSequenceLimit l E Y).map f)) ∧
      ∃ κinv : (integralDerivedPullback l E g).obj N ⟶
          (inverseImageIntegralDerived l E g).obj N,
        κinv ≫ inverseImagePullbackComparisonDerived l E g hX hY N =
            𝟙 _ ∧
          inverseImagePullbackComparisonDerived l E g hX hY N ≫ κinv =
            𝟙 _ ∧
          κinv ≫ (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N) =
            (θ N).hom
```

## New

Current environment commands, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit
```

Current declaration signature, verbatim; it is identical to the original:

```lean
theorem isomorphismDerivedPullbackComparisonNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (hS : Nonempty (CoefficientDerivedSystemCoherence l E Y S))
    (N :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y))
    (hN : IsDerivedCompleteUnrestricted.{t, u} l E Y N) :
    ∃ θ : ∀ M :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y),
      (integralDerivedPullback l E g).obj M ≅
        (inverseImageIntegralDerived l E g).obj
          ((S.reduction ⋙ coefficientSequenceLimit l E Y).obj M),
      (∀ M :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y),
        inverseImagePullbackComparisonDerived l E g hX hY M ≫
            (θ M).hom =
          (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app M)) ∧
      (∀ (M M' :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y))
        (f : M ⟶ M'),
        (integralDerivedPullback l E g).map f ≫ (θ M').hom =
          (θ M).hom ≫
            (inverseImageIntegralDerived l E g).map
              ((S.reduction ⋙ coefficientSequenceLimit l E Y).map f)) ∧
      ∃ κinv : (integralDerivedPullback l E g).obj N ⟶
          (inverseImageIntegralDerived l E g).obj N,
        κinv ≫ inverseImagePullbackComparisonDerived l E g hX hY N =
            𝟙 _ ∧
          inverseImagePullbackComparisonDerived l E g hX hY N ≫ κinv =
            𝟙 _ ∧
          κinv ≫ (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N) =
            (θ N).hom
```

## Users

The read-only downstream scan lists 461 transitive importers. Only
Sheaf.Paper.IsomorphismComparisonNatural and Sheaf.Paper.IsomorphismDerivedPullback
mention the theorem outside its own module; both are unclaimed. All importers
are listed below with their current claim records. Local proof attributes and
elaboration options do not alter imported statements or data. The original
global instance-removal command remains verbatim. Thus there is no forced
adaptation or original compiler error to report. Only the maintainer runs the
global build.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicNormalizedFibreData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AdicStratifiedPullbackInterface` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineSpaceCoordinateBoundaries` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineSpacePurityComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineSpaceThomMap` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryComparisonCompositionTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CofinalFiniteReductionConstructibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportArrowScalarTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportNormalizedRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DirectImagesConstructible` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.DualizingUnitComposite` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.EtaleProEtaleCoefficientTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteCoefficientInputModels` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteRegularCoefficientComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteSiteCounitProjectionTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntrinsicConstructibleFibreExactness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IntrinsicLocalLatticeComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.LocallyClosedRelativeTransposeNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.NormalizedHeartRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.NormalizedLatticeFiniteFree` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationEtaleCoefficientTwists` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationFiniteCoefficientTwists` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationFiniteReductionTwists` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationGeometricComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PerAdicNormalizedFibreComparisons` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointExactDerivedModel` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointTransformationCoefficientDescent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurShiftedTateUnitScalarCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityAffineChartExceptionalIdentification` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalRealizationFiniteConeModels` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | G7 | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RealWeights` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ResidueControlledFiniteHoms` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SignedTateCoefficientExponentNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientationDatum` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientationFamily` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SixFunctorOrientationStageCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | Z7 | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TwConventions` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilGenericLissity` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilInternalHomWeil` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WfTateTwist` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WfTateTwistCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ReductionDirectImageComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ScalarAssociatorConjugate` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenExternalTensorNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.OpenTensorQuotientAugmentation` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | H7 | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | No adaptation; public signature and existing global attributes retained. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No adaptation; public signature and existing global attributes retained. |

## Status

landed 20261022T022041-L-432706 2026-10-22 (merge of deliver/H7/Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization)
