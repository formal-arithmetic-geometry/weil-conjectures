# AlgebraicGeometry.Scheme.completedOpenStrictMateIdentification

## Reason

The proof needs a local transparency option and local irreducibility attributes to
keep the chosen derived-category, adjunction, monoidal and limit constructions from
expanding during elaboration. These are proof-context commands only. All original
public declaration signatures, non-theorem bodies, attributes and public imports
remain identical. The new imports are private proof imports. No target or definition
changes mathematical meaning. No downstream module needs adaptation.

## Old

The old proof-context commands, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
```

## New

The new context retains the old commands and adds the following local controls
(the second attribute appears after the private comparison helpers):

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit

attribute [local irreducible] ProEtale.StrictTower.beta ProEtale.StrictTower.jAdj
  ProEtale.StrictTower.squareG CompletedOpenFiniteTranspose.constantSquare
```

The unit-transpose helper also locally disables the redundant category-to-reflexive-
quiver instance during elaboration:

```lean
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem unit_transpose_eq ...
```

The new private helpers are proved categorical cancellation, comparison and pasting
identities. They do not occur in public signatures or definitions.

## Users

`python3 tools/downstream.py Sheaf.Paper.CompletedOpenStrictMateIdentification --names`
listed the following transitive consumers. Every signature and public construction
is unchanged, so none is edited. Holders are recorded from the current claim files;
no held module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same public interface; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | C9 | Same public interface; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Same public interface; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | P3 | Same public interface; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | V7 | Same public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | A8 | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | A9 | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | E4 | Same public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | T1 | Same public interface; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | Q3 | Same public interface; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same public interface; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | C3 | Same public interface; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Same public interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | T1 | Same public interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | Q8 | Same public interface; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Same public interface; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | R2 | Same public interface; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | U9 | Same public interface; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | Z7 | Same public interface; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | Y7 | Same public interface; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | G2 | Same public interface; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | X3 | Same public interface; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Same public interface; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | P2 | Same public interface; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Same public interface; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | J1 | Same public interface; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same public interface; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same public interface; no adaptation. |

## Status

landed 20261025T201858-L-2634090 2026-10-25 (merge of deliver/F3/Sheaf.Paper.CompletedOpenStrictMateIdentification)
