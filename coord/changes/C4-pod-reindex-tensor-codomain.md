# PodReindexSubstitution and PodReindexingTensorSubstitutionCoreData

## Reason

The two old tensor fields use HEq between natural isomorphisms whose target functors
are independently chosen: the model's sequence-site closed tensor versus
pullbackTensorCalculus.systemClosed.tensor. The calculus pins the reduction functor,
but supplies a canonical closed-tensor isomorphism, not equality of these chosen tensors.
Adjunction uniqueness therefore cannot justify the old HEq requirement. The generic
completed-operation Models interface was already repaired in exactly this direction
on 2026-10-25 (lem-pur-normalized-completed-operation-models.statement_change).

This repair writes the canonical codomain isomorphism explicitly and asks for equality
of isomorphisms after composing with it. Its closed-tensor factor is the comparison
preserving the common internal-Hom adjunction. Its reduction factor is the unique
left-adjoint comparison preserving the common total-limit adjunction. There is no
new free comparison map. It identifies the same fixed strict-tower realization.
The equations still determine qY and qX uniquely, by composing with the two inverses.
No claim that the old stricter HEq specification has been proved is made.

All calculus, completion, Roos and g-pullback pins, the equation involving D.limit,
and ComparisonLaws/SubstitutionLaw/StructuralLaw are unchanged. No target signature
in Challenge.lean is edited, and neither changed definition appears in those signatures.
This is a Sheaf interface correction under brief-stage3 section 4; no adopted
WeilConjectures source is edited. The companion module is unclaimed in the shared snapshot.

## Old

```lean
def PodReindexSubstitution {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D) : Prop :=
  ∃ C : CompletedOperations.Models l E (podReindexLocations X Y),
    ∃ qY : integralCompletedTensor l E Y ≅ IntegralOnSlice.completedTensor l E Y none,
    ∃ qX : integralCompletedTensor l E X ≅ IntegralOnSlice.completedTensor l E X none,
    C.calculus false = podReindexCalculus l E Y ∧
    C.calculus true = podReindexCalculus l E X ∧
    HEq (C.completion false) D.completionSource ∧
    HEq (C.completion true) D.completionTarget ∧
    C.roos false = D.sourceRoos ∧ C.roos true = D.targetRoos ∧
    HEq (C.pullback (a := true) (b := false) g).realization D.pullback ∧
    HEq (qY ≪≫ CompletedOperations.tensorRealization l E C false)
      (pullbackTensorIntegralTensorModel l E Y) ∧
    HEq (qX ≪≫ CompletedOperations.tensorRealization l E C true)
      (pullbackTensorIntegralTensorModel l E X) ∧
    (∀ N : coefficientSequenceDerived l E Y,
      IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
          D.limit.hom.app N) ∧
    PodCompletedTensorReindex.Model l E g D T ∧
    PodCompletedTensorReindex.Canonical l E g D T ∧
    CompletedOperations.ComparisonLaws.{u,u,0,0} l E C ∧
    CompletedOperations.SubstitutionLaw.{u,u,0,0,0} l E C ∧
    CompletedOperations.StructuralLaw.{u,u,0,0} l E C
```

```lean
structure PodReindexingTensorSubstitutionCoreData
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) where
  C : CompletedOperations.Models l E (podReindexLocations X Y)
  qY : integralCompletedTensor l E Y ≅
    IntegralOnSlice.completedTensor l E Y none
  qX : integralCompletedTensor l E X ≅
    IntegralOnSlice.completedTensor l E X none
  calculus_false : C.calculus false = podReindexCalculus l E Y
  calculus_true : C.calculus true = podReindexCalculus l E X
  completion_false : HEq (C.completion false) D.completionSource
  completion_true : HEq (C.completion true) D.completionTarget
  roos_false : C.roos false = D.sourceRoos
  roos_true : C.roos true = D.targetRoos
  pullback : HEq (C.pullback (a := true) (b := false) g).realization D.pullback
  tensor_Y : HEq (qY ≪≫ CompletedOperations.tensorRealization l E C false)
    (pullbackTensorIntegralTensorModel l E Y)
  tensor_X : HEq (qX ≪≫ CompletedOperations.tensorRealization l E C true)
    (pullbackTensorIntegralTensorModel l E X)
  limit : ∀ N : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app
          ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
      D.limit.hom.app N
  comparisonLaws : CompletedOperations.ComparisonLaws.{u, u, 0, 0} l E C
  substitutionLaw : CompletedOperations.SubstitutionLaw.{u, u, 0, 0, 0} l E C
  structuralLaw : CompletedOperations.StructuralLaw.{u, u, 0, 0} l E C
```

## New

```lean
def podReindexTensorCodomainComparison {S : Type s} {W : S → Scheme.{u}}
    (C : CompletedOperations.Models l E W) (a : S) :
    ((C.calculus a).reduction.prod (C.calculus a).reduction) ⋙
        CompletedOperations.tensor l E C a ⋙ coefficientSequenceLimit l E (W a) ≅
      pullbackTensorReferenceTensor l E (W a) :=
  isoWhiskerRight
    (isoWhiskerLeft ((C.calculus a).reduction.prod (C.calculus a).reduction)
        (CoefficientClosedStructure.comparison (C.system a).closed
          (pullbackTensorCalculus l E (W a)).systemClosed) ≪≫
      isoWhiskerRight
        (NatIso.prod
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction)
          (Adjunction.leftAdjointUniq (C.calculus a).adjunction
            (pullbackTensorCalculus l E (W a)).adjunction))
        (pullbackTensorCalculus l E (W a)).systemClosed.tensor)
    (coefficientSequenceLimit l E (W a))

/-- Substitution for these particular normalized primitives. In addition to the
expression laws, both calculi, completion augmentations, Roos models and the
pullback realization are the ones in D. The primitive limit equation involves
D.limit itself. The tensor transport to the slice presentation is fixed by the same
strict tower used in T.Model, whose canonical comparison is T.Canonical.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: def-pod-completion-reindex-substitution). -/
def PodReindexSubstitution {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D) : Prop :=
  ∃ C : CompletedOperations.Models l E (podReindexLocations X Y),
    ∃ qY : integralCompletedTensor l E Y ≅ IntegralOnSlice.completedTensor l E Y none,
    ∃ qX : integralCompletedTensor l E X ≅ IntegralOnSlice.completedTensor l E X none,
    C.calculus false = podReindexCalculus l E Y ∧
    C.calculus true = podReindexCalculus l E X ∧
    HEq (C.completion false) D.completionSource ∧
    HEq (C.completion true) D.completionTarget ∧
    C.roos false = D.sourceRoos ∧ C.roos true = D.targetRoos ∧
    HEq (C.pullback (a := true) (b := false) g).realization D.pullback ∧
    (qY ≪≫ CompletedOperations.tensorRealization l E C false ≪≫
      podReindexTensorCodomainComparison l E C false) =
        pullbackTensorIntegralTensorModel l E Y ∧
    (qX ≪≫ CompletedOperations.tensorRealization l E C true ≪≫
      podReindexTensorCodomainComparison l E C true) =
        pullbackTensorIntegralTensorModel l E X ∧
    (∀ N : coefficientSequenceDerived l E Y,
      IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
          D.limit.hom.app N) ∧
    PodCompletedTensorReindex.Model l E g D T ∧
    PodCompletedTensorReindex.Canonical l E g D T ∧
    CompletedOperations.ComparisonLaws.{u,u,0,0} l E C ∧
    CompletedOperations.SubstitutionLaw.{u,u,0,0,0} l E C ∧
    CompletedOperations.StructuralLaw.{u,u,0,0} l E C
```

```lean
structure PodReindexingTensorSubstitutionCoreData
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) where
  C : CompletedOperations.Models l E (podReindexLocations X Y)
  qY : integralCompletedTensor l E Y ≅
    IntegralOnSlice.completedTensor l E Y none
  qX : integralCompletedTensor l E X ≅
    IntegralOnSlice.completedTensor l E X none
  calculus_false : C.calculus false = podReindexCalculus l E Y
  calculus_true : C.calculus true = podReindexCalculus l E X
  completion_false : HEq (C.completion false) D.completionSource
  completion_true : HEq (C.completion true) D.completionTarget
  roos_false : C.roos false = D.sourceRoos
  roos_true : C.roos true = D.targetRoos
  pullback : HEq (C.pullback (a := true) (b := false) g).realization D.pullback
  tensor_Y : (qY ≪≫ CompletedOperations.tensorRealization l E C false ≪≫
    podReindexTensorCodomainComparison l E C false) = pullbackTensorIntegralTensorModel l E Y
  tensor_X : (qX ≪≫ CompletedOperations.tensorRealization l E C true ≪≫
    podReindexTensorCodomainComparison l E C true) = pullbackTensorIntegralTensorModel l E X
  limit : ∀ N : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y N →
      (podOrdinaryToCompleted l E g D).app
          ((coefficientSequenceLimit l E Y).obj N) ≫
        CompletedOperations.pullbackComparison l E C (a := true) (b := false) g N =
      D.limit.hom.app N
  comparisonLaws : CompletedOperations.ComparisonLaws.{u, u, 0, 0} l E C
  substitutionLaw : CompletedOperations.SubstitutionLaw.{u, u, 0, 0, 0} l E C
  structuralLaw : CompletedOperations.StructuralLaw.{u, u, 0, 0} l E C
```

## Users

The whole-source search for PodReindexSubstitution finds only its defining module,
PodReindexingTensorSubstitution and PodReindexingCompletionUnitTensor. The first consumer
packages the core fields without inspecting their proofs; the second applies that theorem.
The only external user of core.tensor_Y and core.tensor_X is the first consumer.
Both consumers compile unchanged against this delivery, in import order:
PodReindexingTensorSubstitution 5.6 s and PodReindexingCompletionUnitTensor 34.6 s,
without warnings. The changed predicate compiles in 1.7 s and the core in 12.8 s.
Unchanged consumer copies were removed after checking.
No other group's file is adapted. Direct and transitive importers from downstream.py are
listed below; indirect importers keep the same declaration signatures and need no source edits.
Holders are read from the shared snapshot's claim records; they are not new claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | N4 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCochainTensorReindexing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCoefficientRingReindexing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCommonPullbackIdentityUnit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftAgreement | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorFiniteModelCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorFiniteModelExistence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorFiniteModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicIntegralReindexingDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicIntegralReindexingMaps | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicNormalizedPullbackRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicProperOrdinaryPushPreservation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicRealizationComparisonDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingComposition | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingCompositionCancelled | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingHom | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingIdentity | M3 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingTensorCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingTensorIntegral | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingUnitCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicReindexingUnitContraction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicTensorReindexingModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonConstantUnitFrobenius | J3 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonFrobeniusSquareNormalization | G3 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageEvaluationNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA | D2 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ExceptionalRefinementSystemData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusCompactIntegralAmbientNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeProperProjectionComparisons | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeProperProjectionRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedCommonEvaluationForStructure | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedCommonEvaluationNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodCompletedKFlatTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodCompletedOrdinaryTensor | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodIntegralHomComparisonEvaluation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodIntegralHomComparisonIsIso | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodIntegralHomComparisonNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodIntegralHomComparisonTranspose | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodNormalizedTensorSignedShifts | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | R2 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodReindexingCompletionUnitTensor | unclaimed in shared snapshot | Direct importer; unchanged application of podReindexingTensorSubstitution. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | K1 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PodReindexingTensorSubstitution | unclaimed in shared snapshot | Direct consumer; unchanged packaging proof uses repaired core tensor equations. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalConstantUnitFrobenius | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalStalkExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RelativeKunneth | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | J2 | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TensorHomExchange | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VectorBundleThom | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarFiniteScalarCocycles | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarRationalScalarCocycles | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierBiduality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierCoreEquations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierDualInclusion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationRepresentatives | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExactness | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence | Q4 | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationScalar | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierFunctor | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting | R4 | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierScalars | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorInclusion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalHomScalarCounitNormalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalHomScalarEvaluation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalHomScalarEvaluationCore | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.CoefficientCohomologyComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalCounitHomSquares | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalHomTransport | S1 | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitComparison | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.SmoothCoefficientVanishing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingConcentration | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.SmoothDualizingVanishing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.StructuralDualizingIdentification | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| TargetsCheck | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.Statement | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in shared snapshot | No source edit; public declaration signatures unchanged. |

## Status

landed 20261028T020232-L-2483787 2026-10-28 (merge of deliver/C4/Sheaf.Paper.PodReindexingTensorSubstitutionCore)
