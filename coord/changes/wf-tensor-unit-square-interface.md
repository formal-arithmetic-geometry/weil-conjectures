# WeilConjectures.WfTensorUnitSquare tensor-unit interface

## Reason

Separate the coefficient-normalization and augmented-Koszul arguments into reusable statements. Their shared public definitions must precede both modules to avoid an import cycle. Explicit intermediate map types in beta prevent costly inference of total tensor objects.

## Old

Definitions resided in Sheaf.Paper.WfTensorPullbackCompletionUnitSquare.

```lean
abbrev tensor (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ :=
  CochainComplex.mapBifunctor.{u+1,u+2,u+1,u+2,u+1,u+2} U V
    (proEtaleOrdinaryTensor X (ring X d))

abbrev alpha (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :=
  (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
    (coefficientIso X d e) U V).symm

def beta (k : constants X d ⋙ transport X d e ≅ constants X d)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) (m : ℕ) :
    (complexes X d e).obj (tower X d p (tensor X d U V) m) ⟶
      tower X d p (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) m :=
  (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
      (coefficientIso X d e) (tensor X d U V) (koszul X d p m)).inv ≫
    HomologicalComplex.mapBifunctorMap (alpha X d e U V).hom
      ((NatIso.mapHomologicalComplex k (.up ℤ)).hom.app
        (completedKoszulPower (A := A) 1 (fun _ ↦ p) m))
      (proEtaleOrdinaryTensor X (ring X d)) (.up ℤ)
```

## New

The same names are defined in Sheaf.Paper.WfTensorUnitSquareData and publicly re-exported by the original module. Tensor and alpha have their original bodies and explicit types; beta has the same composite with explicitly typed local maps. Other definition bodies and all statement signatures are unchanged.

```lean
def tensor (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ :=
  CochainComplex.mapBifunctor.{u+1,u+2,u+1,u+2,u+1,u+2} U V
    (proEtaleOrdinaryTensor X (ring X d))

def alpha (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    (complexes X d e).obj (tensor X d U V) ≅
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
  (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
    (coefficientIso X d e) U V).symm


attribute [local irreducible] tensor alpha

def beta (k : constants X d ⋙ transport X d e ≅ constants X d)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) (m : ℕ) :
    (complexes X d e).obj (tower X d p (tensor X d U V) m) ⟶
      tower X d p (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) m := by
  let q : (complexes X d e).obj (koszul X d p m) ⟶ koszul X d p m :=
    (NatIso.mapHomologicalComplex k (.up ℤ)).hom.app
      (completedKoszulPower (A := A) 1 (fun _ ↦ p) m)
  let a : (complexes X d e).obj (tensor X d U V) ⟶
      tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V) :=
    (alpha X d e U V).hom
  exact (proEtaleTensorPullbackTotalIso e.hom (ring X d) (ring X d)
      (coefficientIso X d e) (tensor X d U V) (koszul X d p m)).inv ≫
    HomologicalComplex.mapBifunctorMap a q (proEtaleOrdinaryTensor X (ring X d)) (.up ℤ)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WfTensorPullbackCompletionUnitSquare | Q4 | Publicly imports the relocated interface; theorem statement unchanged. |
| Sheaf.Paper.WfCompletedConstantPullbackNormalization | Q4 (new) | States coefficient normalization using the shared definitions. |
| Sheaf.Paper.WfNormalizedKoszulFiberUnitTransport | Q4 (new) | States augmented-tower transport using the shared definitions. |

Current downstream query (2026-10-26) lists the following modules. The original module
publicly reexports all declarations under their original names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | G2 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | R3 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | U9 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.VerdierHomChainComposition | N3 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.Paper.WfTensorCompletionFrobenius | Y9 | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same declaration names and definitionally equal types/bodies; no signature change. |

| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same reexported ring definition; no signature change. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same reexported ring, alpha, and unit; no signature change. |

No source-library module or target signature is changed. These are definitionally
equal constructions, so the mathematical target statements are unchanged.

## Status

landed 20261025T202826-L-2756421 2026-10-25 (merge of deliver/Q4/Sheaf.Paper.WfTensorPullbackCompletionUnitSquare)
