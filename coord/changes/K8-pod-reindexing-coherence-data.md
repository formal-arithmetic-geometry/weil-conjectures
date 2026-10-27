# WeilConjectures.PodReindexingCoherence presentation declarations

## Reason

Four strictly smaller construction/shift statements must use the existing presentation
data and be imported by the item. Moving the presentations to a common module avoids
an import cycle. This is a relocation, not a mathematical or definitional repair.
No adopted source-library module is changed. The item retains all old public imports
and publicly re-exports `Sheaf.Paper.PodReindexingCoherenceData`.

The first delivery compile exceeded the per-file limit in the data module. Profiling
identified structure auxiliary generation repeatedly unfolding derived reindexing
while comparing different coefficient parameters. During this data file only,
`podReindexingDerivedFunctor` and `podReindexingDerivedFactors` are marked locally
irreducible after the common normalization definitions. The later local setting for
the ordinary functor no longer reopens the derived functor. This changes no exported
reducibility attribute, signature or definition value; the imported declarations keep
their original behavior for every consumer.

## Old

The following declarations lived in
`Sheaf.Paper.PodReindexingEvaluationShiftComposition`. Their data bodies are the
existing ordinary, complex and localization constructions and presentation structures.

```lean
abbrev K (W : Scheme.{u}) (s : Option ℕ)

abbrev Closed (W : Scheme.{u}) (s : Option ℕ)

abbrev Models (W : Scheme.{u}) (s : Option ℕ) (S : Closed l E W s)

abbrev total (W : Scheme.{u}) (s : Option ℕ)

abbrev hom (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s)

abbrev proj (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s) (r p q : ℤ) (h : p + r = q)

def signedShift (W : Scheme.{u}) (s : Option ℕ) (M N : podReindexingDerived l E W s) (a b : ℤ) : (podReindexingDerivedHom l E W s).obj (op (M⟦a⟧), N⟦b⟧) ≅ ((podReindexingDerivedHom l E W s).obj (op M, N))⟦b-a⟧

structure Comparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY)

structure EvaluationLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY) (c : Comparison l E g s SX SY TX TY) : Prop

structure ChainShift (W : Scheme.{u}) (s : Option ℕ)

def complexShift {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ) (a : ℤ) : shiftFunctor (K l E Y s) a ⋙ podReindexingComplexFunctor l E g s ≅ podReindexingComplexFunctor l E g s ⋙ shiftFunctor (K l E X s) a

structure ShiftLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY) (c : Comparison l E g s SX SY TX TY) (sX : ChainShift l E X s) (sY : ChainShift l E Y s) : Prop

def siteComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h] : proEtaleIsoPostcompose (h ≫ g) ≅ proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g

structure Compositor {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h] (s : Option ℕ)

def siteId (X : Scheme.{u}) : proEtaleIsoPostcompose (𝟙 X) ≅ 𝟭 X.ProEt

structure Identity (X : Scheme.{u}) (s : Option ℕ)
```

## New

The same declarations, including their full data bodies, now live in
`Sheaf.Paper.PodReindexingCoherenceData`. Only their source docstrings point to the
new definition node. The item publicly imports this module. Every existing declaration
keeps its full name, universe parameters, binders, attributes, signature and value.
The signature comparison against the original found no difference. No target's
mathematical meaning changes and no target signature changes.

The exact new signatures are:

```lean
abbrev K (W : Scheme.{u}) (s : Option ℕ)

abbrev Closed (W : Scheme.{u}) (s : Option ℕ)

abbrev Models (W : Scheme.{u}) (s : Option ℕ) (S : Closed l E W s)

abbrev total (W : Scheme.{u}) (s : Option ℕ)

abbrev hom (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s)

abbrev proj (W : Scheme.{u}) (s : Option ℕ) (P I : K l E W s) (r p q : ℤ) (h : p + r = q)

def signedShift (W : Scheme.{u}) (s : Option ℕ) (M N : podReindexingDerived l E W s) (a b : ℤ) : (podReindexingDerivedHom l E W s).obj (op (M⟦a⟧), N⟦b⟧) ≅ ((podReindexingDerivedHom l E W s).obj (op M, N))⟦b-a⟧

structure Comparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY)

structure EvaluationLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY) (c : Comparison l E g s SX SY TX TY) : Prop

structure ChainShift (W : Scheme.{u}) (s : Option ℕ)

def complexShift {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (s : Option ℕ) (a : ℤ) : shiftFunctor (K l E Y s) a ⋙ podReindexingComplexFunctor l E g s ≅ podReindexingComplexFunctor l E g s ⋙ shiftFunctor (K l E X s) a

structure ShiftLaws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s) (TX : Models l E X s SX) (TY : Models l E Y s SY) (c : Comparison l E g s SX SY TX TY) (sX : ChainShift l E X s) (sY : ChainShift l E Y s) : Prop

def siteComp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h] : proEtaleIsoPostcompose (h ≫ g) ≅ proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose g

structure Compositor {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h] (s : Option ℕ)

def siteId (X : Scheme.{u}) : proEtaleIsoPostcompose (𝟙 X) ≅ 𝟭 X.ProEt

structure Identity (X : Scheme.{u}) (s : Option ℕ)
```

The four additional theorem modules contain only strictly partial source steps,
not a replacement definition or extra hypothesis. The item now proves all logical
assembly, adjunction consequences and Hom compositor/identity equations from those
steps. Existing private proof helpers are retained.

## Users

This table includes the full downstream import closure and declaration-text users
reported by `python3 -B tools/downstream.py
Sheaf.Paper.PodReindexingEvaluationShiftComposition --uses Comparison`, plus the two
direct importers. The broad declaration-text search also reports unrelated generic
Comparison names; they are included conservatively. Claim holders are those of the
shared read-only snapshot on 2026-10-27. No consumer is edited; there is no changed
signature, reducibility attribute or definition body to adapt.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicNormalizedPullbackRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicProperOrdinaryPushPreservation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonConstantUnitFrobenius | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonFrobeniusSquareNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageEvaluationNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedCommonEvaluationForStructure | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedCommonEvaluationNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | unclaimed | Direct importer compiled unchanged against the re-exported identical declarations. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | unclaimed | Direct importer compiled unchanged against the re-exported identical declarations. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | A9 | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| TargetsCheck | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Q1 | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same declarations and public imports remain visible; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same declarations and public imports remain visible; no adaptation. |

## Status

landed 20261027T135435-L-3707416 2026-10-27 (merge of deliver/K8/Sheaf.Paper.PodReindexingEvaluationShiftComposition)
