# WeilConjectures.PurityFiniteSetting.finiteTensorTau

## Reason

The tau reduction statement repeatedly unfolds the native derived tensor/shift
comparison while checking morphism endpoints. With the original reducible
`finiteTensorTau`, even its statement with `by sorry` exceeds the 120-second
run cutoff. Marking the definition irreducible, with its body and inferred type
unchanged, makes that same diagnostic compile in 9.7 seconds. The delivered module keeps the wrapper protected while retaining the original
tau theorem as a named proof hole. No construction or theorem signature changes.

## Old

```lean
def finiteTensorTau (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :=
  (((curriedTensor _).obj M).commShiftIso (2 * (d : ℤ))).symm.app
    (P.finiteTensorFixedLine T d)
```

## New

```lean
@[irreducible] def finiteTensorTau (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) :=
  (((curriedTensor _).obj M).commShiftIso (2 * (d : ℤ))).symm.app
    (P.finiteTensorFixedLine T d)
```

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteTensorPresentationReduction
--uses finiteTensorTau` reports 48 modules importing the item transitively.
Only the item itself contains textual uses of `finiteTensorTau` (three occurrences).
The table records every listed module and its current claim holder. No downstream
adaptation is needed: the construction, its type and every theorem statement stay
identical, and no downstream declaration refers to tau.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTensorPresentationReduction | M7 | Same body and type; protect tau while checking its unchanged theorem statement. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No textual use of finiteTensorTau; signatures and definition data unchanged. |

The public construction and its inferred type are identical. No target statement
changes meaning. The only interface difference is definitional transparency.

## Status

landed 20261026T002034-L-51579 2026-10-26 (merge of deliver/M7/Sheaf.Paper.FiniteTensorPresentationReduction)
