# WeilConjectures.GeneratorReduction.completionMap_isIso

## Reason

The parent proof imports the tensor/adjunction lemma and four forward open-square lemmas. The
tensor-square module currently imports the parent and uses the proved
completionMap_isIso five times. The earlier K4 landing was taken out because its
import-only repair lost that helper (coord/build-errors/Sheaf.SixFunctors.TensorAdjunctionReductionSquares.txt).
Move the existing completion theorem, with exactly the same name, signature,
docstring and proof, to an independent module. The parent publicly re-exports it.
No operation definition, coefficient comparison, target statement, theorem
signature or theorem meaning changes. No target meaning review is reopened.
The extraction is required by import ordering, not by a file-timeout workaround.

The original tensor import closes a cycle after the parent's new proof imports:
GeneratorReductionStatement -> TensorAdjunctionReductionSquares ->
GeneratorReductionStatement. This exact error was reproduced by lcompile.py in
scratchpad/original-cycle. Tensor is unclaimed in the current claim snapshot;
its sole changed line redirects that import. All four delivered modules compile
in dependency order.

OpenInterchangeReductionSquares was concurrently updated during this session.
It now imports OpenInterchangeReductionData independently and has a completed
proof. Our earlier stale copy was removed; that module is not delivered or
changed. Its public theorem signature is unchanged. The final parent proof uses
the four forward case lemmas directly and does not import the larger package or
its auxiliary CanonicalOpenReductionIsIso. The parent node records the exact
replacement proof edges. StructuralReductionWordSubstitution likewise imports
only the independent data, preserving its recorded statement.

## Old

In Sheaf.SixFunctors.GeneratorReductionStatement:

```lean
theorem completionMap_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (_hLength : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K)
```

TensorAdjunctionReductionSquares publicly imports Sheaf.SixFunctors.GeneratorReductionStatement.

## New

The identical theorem in Sheaf.SixFunctors.ShortWordCompletionIsomorphism:

```lean
theorem completionMap_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (_hLength : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K)
```

The item publicly imports Sheaf.SixFunctors.ShortWordCompletionIsomorphism while
retaining its existing public import of GeneratorReductionData. Tensor now
publicly imports ShortWordCompletionIsomorphism. All tensor declarations and
proof bodies are byte-identical. The obsolete public parent re-export cannot
coexist with the required import direction. Tensor has zero existing importers,
so no external consumer loses a parent declaration.

The two completion-isomorphism DAG attachments follow the moved theorem. The
existing substitution node and its recorded statement are restored without any
statement change; the earlier take-out removed its Lean file but kept the node.

## Users

The mandated tools/downstream.py --uses completionMap_isIso scan found 526 transitive
item importers, of which only the item and tensor-square module mention the moved
name. All retain the same theorem through public re-export. The tensor-square module has zero existing downstream importers. Every transitive item
importer and every changed module is listed below; no source-library module is
changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | H2 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | D3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | T9 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | Z7 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | G8 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | V3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | J7 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | D4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | J2 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | T1 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | S6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | N4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | U6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | S3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | S6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | G7 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | B6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | H5 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | X3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | P1 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | W6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | A5 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | T9 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | N3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | V6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | B9 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | B4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | C3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | U6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | V8 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | W7 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | N3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | W4 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | R2 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | X5 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | F1 (assigned) | Publicly re-exports moved helper; proves coherence. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | J6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | Z6 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | S8 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | new in this delivery | Contains the existing proved helper verbatim. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | restored in this delivery | States the existing DAG node, unchanged signature. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Single import redirects to independent helper; proofs and signatures identical. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | H3 | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Unchanged public API through the item re-export; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Unchanged public API through the item re-export; no adaptation. |

## Status

landed 20261026T001415-L-4190115 2026-10-26 (merge of deliver/F1/Sheaf.SixFunctors.GeneratorReductionStatement)
