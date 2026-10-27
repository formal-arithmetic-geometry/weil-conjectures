# compositionInverse

## Reason

The direct concrete expression caused a deterministic kernel timeout when proving
its invertibility in CoordinateSectionArrows. Cache the category parameters using
the generic irreducible `transposeComposition`. Its unfolding is the original map,
so the target meanings and all existing signatures are preserved. All added
helpers have complete proofs or concrete construction bodies. No source-library
module is edited. The definition change is submitted for independent review.

## Old

```lean
def compositionInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace T] [CompactSpace S]
    (K : Plus A S) :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj K.obj) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K.obj :=
  rightDerivedUpperShriekHomEquiv (f ≫ g)
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g K.property)) K.property
      ((originCompositionAmbient A f g).inv.app
        ⟨_, plusEtaleOrigin_rightDerivedUpperShriek_obj f
          (plus_rightDerivedUpperShriek_obj g K.property)⟩ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g K.property)) ≫
        rightDerivedUpperShriekCounit g K.obj K.property)
```

## New

```lean
def compositionInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace T] [CompactSpace S]
    (K : Plus A S) :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj K.obj) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K.obj :=
  transposeComposition
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekHomEquiv (f ≫ g)
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f
        (plus_rightDerivedUpperShriek_obj g K.property)) K.property)
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekCounit g K.obj K.property)
    (originCompositionAmbient A f g)
```

The generic helper is in the same module and attached to its existing node.

## Users

The following is the complete downstream list from `tools/downstream.py Sheaf.Paper.AffineSpacePurityComparison --uses compositionInverse`, including the defining module.
The declaration-use search finds AffineLineCompositeTranspose, AffineSpacePurityComparison, AffineSpacePurityComposition, AffineSpaceZeroSectionPurity, CoordinateSectionArrows and CoordinateTowerNormalizationInduction.
No downstream proof unfolds the changed definition. The canonical map, its
endpoints, and every existing statement are unchanged; no forced consumer edit
is required.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineIntegrationExponentTransition` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineLineCompositeTranspose` | C1 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | K4 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpaceCoordinateBoundaries` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | H2 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | definition-preserving cached implementation |
| `Sheaf.Paper.AffineSpacePurityComposition` | F1 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpaceThomMap` | E3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | D3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | D4 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDiagonalAssemblyData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDiagonalSourceMate` | H3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDiagonalSourceSquare` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDncNaturality` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDncSquare` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDncVectorFactorData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartEpsilonPasting` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartExceptionalCounitEquation` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartIntegrationAdjoints` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartNormalIntegrationSquare` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateSectionArrows` | C6 | proof filled in this delivery |
| `Sheaf.Paper.CoordinateSectionProductRecursion` | Y8 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateSectionProjection` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateTowerNormalizationInduction` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateZeroBaseChange` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineIntegrationSiteSquare` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineRankZeroActual` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineTraceCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineTraceMapAgreement` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineTraceSiteComparison` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalAffineTraceSiteData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalDncAssemblyGlobal` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalDncChartNormalization` | T5 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | V3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.EvenLineProductIntegrationSymmetry` | J4 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | F1 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.FiniteProductReductionComparisons` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.FiniteReductionOfPurity` | S3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.GeneralChartComparisons` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ModelAffineIntegrationOrientation` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ModelChartOrientationAssembly` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ModelOrientationChartDescent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ModelOrientationSourceNaturality` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ModelOrientationTateDetection` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.NormalModelSectionOrientation` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | X3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.OrderedAffineTransposeProjection` | S3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.ProjectionPurityAgreement` | X3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.PurityCompositionCompatibleDncCharts` | P1 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.RetaggingCoordinateOrientations` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SectionDncIntegrationSquare` | N3 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorBundleFrameOrientationRestriction` | Y8 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorIntegrationChartTranspose` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorIntegrationUnitTranspose` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed | signature and statement unchanged; no edit needed |

## Status

landed 20261025T205426-L-3236278 2026-10-25 (merge of deliver/C6/Sheaf.Paper.CoordinateSectionArrows)
