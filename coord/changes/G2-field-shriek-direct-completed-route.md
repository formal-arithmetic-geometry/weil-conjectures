# FieldShriekCompositionQcqs direct completed-ring proof route

## Reason

Repair of the return of G2 delivery `8a84392fd79`: each of the three newly
split realization lemmas inherited a DAG path through coefficient conventions,
Frobenius cohomology and `lem-zl-field-shriek-composition-qcqs` back to the item.
The latter node was the only reachable node with a direct dependency on the item.

The field-shriek module already defines `sfCompositionLambda`, its inverse open
adjunct `sfCompositionGamma`, and `sfCompletedCompositionOnTower` directly in the
completed ringed derived categories. Its theorem statements therefore do not need
the full expression-system realization package. The repaired sourced argument uses
open restriction exchange, the existing proper/open coefficient comparisons,
complete-cone conservativity, the published qcqs realization, and normalized
refinement coherence. It constructs the same specified completed-ring comparison
before rationalization and finite-stage descent. All three original theorem holes
remain; no theorem is weakened, removed, or replaced by a new hole.

The module is unclaimed at the consumer audit. Only its private proof import and
its integral theorem's proof-in-words docstring change. The node's `proof`,
`proof_deps` and `proof_origin` follow that direct route. Its statement,
statement dependencies, Lean attachment and unit realization remain unchanged.
No source-library module is edited and no target statement or meaning changes.

## Old

```lean
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
```

The old node proof invoked `lem-sf-integral-compactification-system-realization`
for construction, finite evaluation and pasting of Gamma and then for transport
of the compatible-tower composite.

## New

```lean
import Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent
```

The repaired node proof uses the actual completed-ring maps already defined in
this module. Open restriction exchange gives invertibility of the specified
lambda; its inverse open adjunct is the displayed Gamma. Actual coefficient mates
identify its finite reductions. Completeness and vanishing of the cone reductions
prove invertibility, and open-adjunction injectivity proves pasting. The normalized
qcqs comparison and refinement coherence then give the recorded integral
compositor and uniqueness. Rationalization and common-stage descent are unchanged.
The old dependency on the full system-realization theorem is removed, rather than
routed through either of the new realization obligations.

## Users

The read-only command `python3 tools/downstream.py Sheaf.Paper.FieldShriekCompositionQcqs
--uses sfFieldShriekCompositionIntegral_existsUnique
sfFieldShriekCompositionRational_existsUnique sfFieldShriekCompositionQbar_existsUnique`
listed 354 transitive importers. The integral and rational existence theorems are
used only in this module; the qbar existence theorem is also used in
`Sheaf.Paper.WeilCompactSupportCohomology`. Existing signatures, bodies, attributes
and public imports are byte-for-byte unchanged, so every consumer sees the same
interface. There are no forced adaptations. The full consumer list follows.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Private proof import and sourced proof plan changed; signatures, bodies and public imports unchanged. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | C9 | Unchanged public interface; no adaptation required. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.FourierTransform.FourierDeligneTransform` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicExceptionalShiftCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | W2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | R2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicTraceTensorShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | W3 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | D4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | G4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | G7 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CommonStageWeilShriek` | C6 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompletedHomScalarTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | A2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantDirectImageTowerRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionPullbackReturnResidue` | J2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionReturnLocalOperators` | Q4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionSheetHeartCoordinates` | A7 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | B2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstructibleExceptionalCompositor` | D8 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstructibleMateCoherence` | R1 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ConstructibleWeilModelSquares` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | T1 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FieldCohomologyPerfectDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | T3 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteCompactSupportCoefficientSquare` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteRationalHeartComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteSheafH0Augmentation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcComparisonData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcIntegralComparisonLaws` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcRawComparisonData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrameworkPbcRawComparisonLaws` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | Q3 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence` | H5 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusSquareExchange` | H6 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | J7 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | C6 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IdentityCompactificationSystemMate` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IntegralDualizingExceptionalUnit` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IntegralSectionsPerfectReduction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.IntegralSemilinearGermSquare` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.InverseContravariantBidual` | D7 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | V2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | W2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.NormalizedSupportEtalePresentation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PointEquivariantDiagramLift` | R6 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PointWeilHeartFlag` | J4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | Y5 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | P4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | X6 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ProperWeilIterateGermFormula` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalOrdinaryCohomologyTensor` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | E1 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | T1 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SemilinearGermIterationDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | E2 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | B9 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TensorAdjunctionExchange` | S1 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.VerdierCompositionMateNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | X3 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | J3 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | S4 | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | U4 | Unchanged public interface; no adaptation required. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefficientUnitFiniteTor` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CoefficientUnitNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CompactifiedProperTowerExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.CompletedSystemPullbackPreservation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemDuality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | N3 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteExceptional` | X3 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteMappingAdjunctionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescent` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | Z6 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralDualizing` | Z6 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralSystemDualityCompatibility` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralVerdierModels` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.IntegralVerdierSignedCalculus` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | A5 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalHomIdentifications` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalOperationsData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RationalVerdier` | B6 | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.TensorHomTranspositionData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.VerdierExchangeData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.CompactDirectPowerTransportNormalization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.FrobeniusCompactPowerExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.FrobeniusProperPowerExchange` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.TraceFormula.LocalNormalizationStrictRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Unchanged public interface; no adaptation required. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unchanged public interface; no adaptation required. |

## Status

landed 20261025T122945-L-1820354 2026-10-25 (merge of deliver/G2/Sheaf.SixFunctors.IntegralCompactificationSystemRealization)
