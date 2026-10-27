# WeilConjectures.IntegralSupportNormalization.Normalization

## Reason

Extract the existing support-normalization definitions to
`Sheaf.Paper.IntegralSupportNormalizationData` and publicly re-export that module
from `Sheaf.Paper.IntegralSupportFunctorNormalization`. Separate open and closed
proof obligations can then import the definitions without importing their consumer,
which would create an import cycle. Every existing public name, type, structure field
and definition body is preserved. The previously proved identity existence/uniqueness
result moves with its definitions; its extensionality proof now calls a proved private
sectionwise-uniqueness helper with abstract ring and functor, avoiding completed-limit
unfolding. The exact existing declaration bodies, not new arbitrary chosen data, are used.

No target statement or the meaning of a definition it uses changes. The independent
reader should verify the extracted signatures and bodies and the public re-export.
No consumer adaptation is necessary. No source-library module is edited.

## Old

The following signatures are declared directly in
`Sheaf.Paper.IntegralSupportFunctorNormalization`:

```lean
abbrev ordinaryOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

def identityModuleImage (X : Scheme.{u})

def identityImage (X : Scheme.{u}) :
    proEtaleRingDerivedDirectImage (𝟙 X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull (𝟙 X)) ≅
      𝟭 (DerivedCategory (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X)))

def openIdentity {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PurCompactSupport.image (PurCompactSupport.completed l E)
        (Compactification.ofIsOpenImmersion j) ≅ ordinaryOpen l E j

def closedReduction {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) :
    sfOrdinaryDerivedPull l E i ⋙ FrobeniusExchange.reduction l E Z ⟶
      FrobeniusExchange.reduction l E X ⋙ integralComparisonDerivedSequencePullback l E i

def closedLimit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) [IsIso (closedReduction l E i C)] :
    coefficientSequenceLimit l E Z ⋙ sfCompletedDerivedDirectImage l E i ≅
      FrobeniusExchange.systemDirect l E i ⋙ coefficientSequenceLimit l E X

def closedAlpha {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) [IsIso (closedReduction l E i C)] :
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i ⟶
      (sfIntegralConstructible l E Z).ι ⋙ FrobeniusExchange.integralDirectImage l E i

abbrev ordinaryOpenPull {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

def ordinaryOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ordinaryOpen l E j ⊣ ordinaryOpenPull l E j

def systemDirectId (X : Scheme.{u}) :
    FrobeniusExchange.systemDirect l E (𝟙 X) ≅ 𝟭 (coefficientSequenceDerived l E X)

instance limitShift (T : Scheme.{u}) : (coefficientSequenceLimit l E T).CommShift ℤ

instance reductionShift (T : Scheme.{u}) : (FrobeniusExchange.reduction l E T).CommShift ℤ

instance directShift {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (FrobeniusExchange.integralDirectImage l E i).CommShift ℤ

def directEvaluationIso {Z X : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)

structure Normalization (D : FiniteFieldDatum.{u})
    {Z U X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
```

The proved `identityModuleImage_existsUnique` is in the same module, immediately
before the unique-choice identityModuleImage definition.

## New

The signatures, structure fields and bodies listed above are unchanged, and are
now declared in `Sheaf.Paper.IntegralSupportNormalizationData`. The old module has:

```lean
public import Sheaf.Paper.IntegralSupportNormalizationData
```

Its main theorem retains its exact original signature and now assembles two strictly
smaller, separately named open and closed obligations. Existing definition-owner node
attachments are updated to the new module. No old declaration is withdrawn.

## Users

The complete transitive consumer list from tools/downstream.py follows. Every consumer
gets the same declarations through the old module's public re-export, including the
same structure projection names and definitional bodies. Holder records were read
when preparing this table. None is edited in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | B9 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | W3 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | V7 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | Q3 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | V4 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | T1 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | B9 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | U5 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | D2 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | X3 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | W4 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | S9 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | U4 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | A5 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | F2 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | X5 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Identical declarations through public re-export; no source adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | A2 | Identical declarations through public re-export; no source adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | Y2 | Identical declarations through public re-export; no source adaptation. |

## Status

landed 20261025T122724-L-1799577 2026-10-25 (merge of deliver/D6/Sheaf.Paper.IntegralSupportFunctorNormalization)
