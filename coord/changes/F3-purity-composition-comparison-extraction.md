# Purity composition comparison declarations

## Reason

The composition theorem needs the existing model-orientation descent theorem. Its
coordinate definitions imported PurityCompositionCoherence for comparison data,
so using it from that theorem would close an import cycle. Extract all 38 existing
comparison declarations unchanged into PurityCompositionComparisons. The item
publicly imports that module; CompositionModelOrientationDefinitions imports the
comparison module directly. No definition, signature, visibility or normalization
of any existing declaration changes. No source-library module is modified.

## Old

The existing comparison declarations, from compositionTwistShift through
compositionExceptionalIso, are defined in Sheaf.Paper.PurityCompositionCoherence.
CompositionModelOrientationDefinitions contains this import verbatim:

```lean
public import Sheaf.Paper.PurityCompositionCoherence
```

## New

The same declaration text is in Sheaf.Paper.PurityCompositionComparisons and the
item publicly imports it. CompositionModelOrientationDefinitions changes exactly
its import line to:

```lean
public import Sheaf.Paper.PurityCompositionComparisons
```

The extracted declarations have byte-identical docstrings, signatures and bodies.
All original public imports remain publicly available through the comparison
module. The two private standing-inverse proof imports move with the proofs that
use them. The coherence theorem retains its original signature and visibility.
The comparison node's Lean attachment follows its declarations; the theorem node
retains only its own declaration in its attachment.

The orientation-definition module intentionally stops re-exporting the coherence
theorem itself: retaining that re-export would recreate the cycle. Its six existing
transitive consumers (CompositionModelOrientationDescent,
ModelAffineIntegrationOrientation, ModelChartOrientationAssembly,
ModelOrientationChartDescent, ModelOrientationSourceNaturality and
ModelOrientationTateDetection) contain zero uses of smoothPurityCompositionCoherence
(tools/downstream.py --uses). The only external Lean user of that theorem,
FiniteReductionOfPurity, already imports PurityCompositionCoherence directly.
Thus no consumer adaptation is required for the removed theorem re-export.

## Users

The table covers every downstream module returned by tools/downstream.py for the
item. No user's mathematical statement changes. Claim holders are the local
read-only snapshot; unclaimed means no local claim record. Except for the one
import edit, existing consumers require no changes because the names and public
re-exported interfaces are identical. The full proposed import graph is acyclic.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Import comparison data directly to avoid the cycle; all declarations unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | G4 | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | M7 | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | Y7 | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing declarations retain their signatures and meaning; no source adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | F3 (dispatcher assignment) | Publicly re-export comparison data; prove original theorem from coordinate lemmas. |

## Status

landed 20261026T001447-L-738 2026-10-26 (merge of deliver/F3/Sheaf.Paper.PurityCompositionCoherence)
