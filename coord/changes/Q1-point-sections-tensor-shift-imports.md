# Sheaf.Paper.PointSectionsTensorShift public imports

## Reason

The proof uses the existing normalized sections-tensor comparison and the source
library's generic shift API. The independent-universe constant-map construction and
finite coefficient quotient theorem are unused. Remove their public imports as
part of pruning. No declaration, signature, definition, instance or visibility is
changed. The sole direct importer uses a private import of this item and compiles
unchanged against the reduced imports, so its own public export surface is unaffected.

## Old

```lean
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
```

## New

Both unused public imports are removed. The public import of
`Sheaf.Paper.PointSectionsScalarExtension` is retained; the source shift API is
imported privately. Every original declaration and signature is retained verbatim.

## Users

The table lists the transitive source import closure, including twelve additional
consumers found by a fresh source-import scan on 2026-10-19. No consumer is adapted;
the holding-group entries describe the earlier inventory where known. Only `Sheaf.Paper.PointFibreEquivalence` directly imports the
item. No consumer source change is required. Its unchanged source compiled in the
same sandbox after the new item, both within the single-file limit.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPurityObjects | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ArithmeticRoots | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FiniteTorStability | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FourierTraceFormula | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.InternalHomPullback | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.IteratedWeilMap | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | unchanged; compiled against the delivered module |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.PurityDncInvariance | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.RationalStalkExact | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.SfBidualityClass | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.SmoothPurityMap | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.SmoothTrace | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFixedScheme | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.TwConventions | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.WeilFourierInversion | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.WeilOne | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.Paper.ZlShriekComposition | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.RationalOperations | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | unchanged; sole direct importer imports the item privately |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | unchanged; sole direct importer imports the item privately |
| TargetsCheck | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.Statement | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.Curve | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.Examples | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | unchanged; sole direct importer imports the item privately |
| WeilConjectures.ZetaFunction.Weights | unclaimed | unchanged; sole direct importer imports the item privately |

| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.DlConstantFieldCharts | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.ProperCoincidenceFrobenius | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | unchanged; behind the private direct import |
| Sheaf.Paper.TraceFormulaAdicSystem | not adapted | unchanged; behind the private direct import |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted | unchanged; behind the private direct import |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not adapted | unchanged; behind the private direct import |

## Status

landed 20261019T005401-L-2762049 2026-10-19 (merge of deliver/Q1/Sheaf.Paper.PointSectionsTensorShift)
