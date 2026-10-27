# WeilConjectures.IntegralSystemRealization.RingedModels

## Reason

The existing `tensorClosed` equates functors but leaves the ordinary tensor's representative
isomorphism unrelated to the coefficient calculus's representative isomorphism. Multiplying
that isomorphism by minus one and multiplying its completion comparison by minus one
preserves `Tensor.canonical`, `RingedModels.tensorClosed`, and all their old fields, while
negating `tensorCompletion` and `tensorR`. Thus the old interface did not imply the specified
primitive transpose equality. The blueprint explicitly requires the canonical independently
normalized ringed maps. The new `tensorRepresentative` equation fixes this missing
normalization on every pair of good representatives; it is a representative equation, not
the generator square or the desired transpose formula.

The source is the current blueprint fix-prop-coherence.proof.md, maps-used sentence, together
with the canonical ringed-site normalization of def-sf-integral-system-canonical-bridge.
There are no new data choices and no holes in the repaired structure. No source-library
module is changed. Challenge declarations stay verbatim; their use of this canonical model
interface merits the normal independent statement review.

## Old

```lean
structure RingedModels where
  tensor : ∀ W : Scheme.{u}, OpenFactorCoherence.Tensor l E W
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), OpenFactorCoherence.Pull l E f
  tensorClosed : ∀ W : Scheme.{u},
    (tensor W).ordinary.tensor = (calculus l E W).integralClosed.tensor
```

## New

```lean
structure RingedModels where
  tensor : ∀ W : Scheme.{u}, OpenFactorCoherence.Tensor l E W
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), OpenFactorCoherence.Pull l E f
  tensorClosed : ∀ W : Scheme.{u},
    (tensor W).ordinary.tensor = (calculus l E W).integralClosed.tensor
  /-- The functor equality also preserves the specified total-complex representatives. -/
  tensorRepresentative : ∀ (W : Scheme.{u})
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) P)
    (hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) Q),
    (tensor W).ordinary.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
      (eqToIso (congrArg (fun T ↦ T.obj (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) (tensorClosed W))).hom =
    ((calculus l E W).integralTensorModel.iso (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (calculus l E W).integralClosed P Q ((tensor W).good P hP).1
        ((tensor W).good Q hQ).1).hom
```

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralSystemCanonicalBridge --uses RingedModels`
was inspected in full. No consumer constructs `RingedModels` or uses its recursor; its users
accept the canonical model as an argument or a structure field. No consumer adaptation is
forced. The unchanged direct users are compiled against the repaired module in this packet's
validation. The full downstream audit follows.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | K4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | S7 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CommonStageWeilShriek | C6 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | S4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.Paper.CompletedHomScalarTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CompositionTensorMate | G8 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | A2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | W9 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | H5 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusSquareExchange | H6 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GeometricOperations | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PointEquivariantDiagramLift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | P4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | X6 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TensorAdjunctionExchange | S1 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VectorIntegrationChartComparison | Z9 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VectorModelChartDescent | W7 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | J3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | R2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | H4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.CompositionProjectionMate | U7 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | S2 | Item proof uses the normalization through the new augmentation lemma; its theorem signatures stay verbatim. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralBasicRealization | T1 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | G2 | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | T2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | E3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | C2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | D2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | E2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.RationalOperations | D2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.SixFunctors.RefinementProjectionCounit | T3 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | C2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.ThreeCellCompositor | J2 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | T4 | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive consumer; canonical operations and all existing field projections unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Abstract consumer; no construction or pattern match on RingedModels; interface compiles unchanged. |

## Status

landed 20261025T095817-L-3484356 2026-10-25 (merge of deliver/S2/Sheaf.SixFunctors.GeneratorReductionStatement)
