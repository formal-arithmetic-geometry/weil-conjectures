# AlgebraicGeometry.ProEtale.VectorIntegrationSite.projectiveB_isIso

## Reason

The proof compares the actual unit and Chern adjuncts and assembles their
biproduct. Private proof helpers and transparency settings keep the existing
canonical derived constructions aligned without changing their data or any
public interface. No existing non-theorem body changes.

## Old

The original theorem was:

```lean
theorem projectiveB_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    IsIso (projectiveB l E n S hS hI r hA) := by
  sorry
```

The file's elaboration settings were:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
```

## New

The theorem is proved from the existing supported Chern comparison and the
ordinary projective-line decomposition, using proved private adjunction and
biproduct helpers. Both added imports are private proof imports.

A proof section enables backward defeq attributes and respects local transparency.
The overlapping Cartier cache instances are disabled for proof elaboration, and
explicitly restored with their original attributes before `projectiveTrace`.
All other attribute changes use `local`. All option changes are section-scoped.
The original definitions and their original elaboration context are preserved.
No public signature refers to a private helper. There are no new public theorems,
no new definitions, no adapted consumers and no forced adaptations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | E5 | Fill projectiveB_isIso; proof context only. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | C1 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | E3 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | D4 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | J1 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | X2 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | X3 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | G9 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | B9 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | C6 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Y8 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | R2 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | C8 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | J2 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | F1 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | V7 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.LineCounitComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | W8 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | N3 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | R9 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | Q1 | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Public interface unchanged; no source adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Public interface unchanged; no source adaptation. |

No consumer adaptation is required. Local commands end and instance attributes are restored before the next
existing definition. The target statements and all definitions they use retain
their original signatures and bodies.

## Status

landed 20261026T001331-L-4185056 2026-10-26 (merge of deliver/E5/Sheaf.Paper.ProEtaleProjectiveLineTrace)
