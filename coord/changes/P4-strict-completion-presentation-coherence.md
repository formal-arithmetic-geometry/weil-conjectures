# TrfCompletionRoosNormalized

## Reason

The original every-presentation clause is false. CoefficientReductionPresentation
constrains e only after finite derived evaluation. Conservativity of evaluations
does not imply faithfulness on morphisms. The invisible-twist counterexample in
coord/reports/T6/Sheaf.Paper.PrimitiveQuotientRealizationComparisons.md applies
already to the identity map and to this completion-only assertion.

For A = Z_p, let B be the completed countable free A-module, and let D = product_i A.
Embed B in D by (b_i) mapped to (p^i b_i), and put M = coker(B -> D).
B and D are complete and torsion-free, so this two-term presentation makes M derived
complete. The class x of (p^i)_i is nonzero, since (1)_i is not in B, but x lies in
every p^n M by subtracting the first n coordinates. On K = A direct-sum M the map
sending 1 to x and vanishing on M is nonzero and square zero. Its derived reductions
are zero, because it is divisible by every p^n. Thus 1+delta gives an automorphism
invisible at each finite derived evaluation, while completion detects it.
Twisting e by its reduction preserves the old hypotheses and the same kappa.
The required section formula fixes the strict tower isomorphism a, so the two limit
equations would force the completion of this automorphism to be the identity.
This is the prior reviewed mathematical obstruction, not a Lean-certified negation.

Require the existing IsIntegralComparisonPresentationCoherent predicate, exactly
as the related pullback normalization was corrected by S9. It pins e by two
adjunction Hom bijections to the localization of the strict tensor-unit map.
The construction now compares whole systems before taking a limit. This is an
explicit auxiliary-interface correction; it does not prove the old false clause.
The actual quotient tower, all section formulas, Roos comparison, good class,
coefficient categories and all theorem signatures remain unchanged.

The completion-unit consumer uses the canonical ordinary/derived model
presentation. Its coherence follows from derivedTranspose applied to the identity
and ordinary_unit_section. These are already proved and add no hypothesis to that
theorem. All other users either carry the named predicate or use unchanged tower
notation. No definition used to state a Challenge target is changed: this predicate
occurs only in the comparison proof interface. Canonical coherent presentations exist
for every good P by coherentPrimitiveReductionPresentation, without geometric,
boundedness or completeness hypotheses. Empty schemes, zero complexes and the
exponent-one quotient use the same adjunction formulas.

## Old

```lean
def TrfCompletionRoosNormalized (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (r : IntegralComparisonRoosModel l E W)
    (rho : integralOperationsGoodLocalization l E W ⋙
        (S.reduction ⋙ coefficientSequenceLimit l E W) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ trfQuotientTowerFunctor l E W ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj K)
    (kappa : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj K ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj),
    CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 K e kappa →
    ∃ a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        K).asFunctor ≅ (trfQuotientTowerFunctor l E W).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (K.X i).val.obj (op (n, U.unop))),
        ((a.hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l E W (K.X i) n U x) =
          ((kappa n).hom.f i).val.app U
            (coefficientEvaluationSection l E W (K.X i) n U x)) ∧
      rho.hom.app P =
        (coefficientSequenceLimit l E W).map e.hom ≫
          (integralComparisonRoosBridge l E W r K).hom ≫
            DerivedCategory.Q.map (integralOperationsRoosFunctor.map a.hom)
```

## New

```lean
def TrfCompletionRoosNormalized (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (r : IntegralComparisonRoosModel l E W)
    (rho : integralOperationsGoodLocalization l E W ⋙
        (S.reduction ⋙ coefficientSequenceLimit l E W) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ trfQuotientTowerFunctor l E W ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj K)
    (kappa : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj K ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj),
    CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 K e kappa →
    IsIntegralComparisonPresentationCoherent l E W S P.obj K e kappa →
    ∃ a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        K).asFunctor ≅ (trfQuotientTowerFunctor l E W).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (K.X i).val.obj (op (n, U.unop))),
        ((a.hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l E W (K.X i) n U x) =
          ((kappa n).hom.f i).val.app U
            (coefficientEvaluationSection l E W (K.X i) n U x)) ∧
      rho.hom.app P =
        (coefficientSequenceLimit l E W).map e.hom ≫
          (integralComparisonRoosBridge l E W r K).hom ≫
            DerivedCategory.Q.map (integralOperationsRoosFunctor.map a.hom)
```

## Users

The shared mirror has no claim record for either adapted existing module.
The assigned module is held by P4. The quarantine copies of these same paths are
preserved untouched; their dependent presentations have the same audit below.
The source tree remains intact. The four direct importers are the assigned item,
IsomorphismStrictQuotientMultiplication, IsomorphismQuotientRoosComparison, and
IsomorphismMultiplicationConeDescent. The indirect completion-unit consumer is
adapted by the coherence proof described above.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.AllStageCtfPullbackUnit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.AmbientComparisonSystemExistence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.AugmentedIntegralDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.AutomorphismSquareRationalScalar` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ClopenCommonCompactSupport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ClopenIntegralRestriction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ClopenRoosIntegralDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CoefficientDualModelTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageEvaluationNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStagePullbackCompNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageShiftedUnitTensor` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageTensorBraidingNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageTensorLineCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageTensorRightUnitorNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageWeilIterate` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CommonTensorBraidingNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientFamilyTransportModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientNormalizedTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientSystemTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientTensorTransportModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedCoefficientTransportExpressions` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedComparisonCanonicalIdentification` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedComparisonQuotientNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedComparisonScalarLimitImage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedConstantRightUnit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedInverseImageScalarCounit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedOpenTensorSystemRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitAdmissible` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitMultiplicationComponents` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitPullbackData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitPullbackTower` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitReduction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitScalarNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.CompletedUnitStrictComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstantTwistCoefficientComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstantWeilStageCompatibility` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DlLocalHeartAbelianEvaluation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DlLocalHeartCoverBasisZero` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DlLocalHeartCoverDefects` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.EffectiveQuotientModelDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ExplicitScalarConeWordCoordinates` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdCompletionFiniteStageLinear` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdIntegralInverseScalarCocycle` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdIntegralScalarDescentInputs` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteCompositorCounit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProductEvaluationSwap` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProductNormalForm` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProperCompositorMate` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProperProductMaps` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProperProductTranspose` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteProperTransportTranspose` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteRegularCoefficientComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteRestrictionConstructibleVertices` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteRestrictionDiagramModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FiniteRestrictionStrictTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FourierTrivialCharacterUnit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FrobeniusFixedPairComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralCoherenceData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonCanonicalShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonCompositionReduction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonPullbackRealizationShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonScalarRealizationShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralExpressionSystemComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralGoodQuotientPresentation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralReductionClopenComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralReductionFiniteClopenBounds` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStratumChartRestrictions` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsCharts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsFunctorial` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStrictExpressionRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStrictPullbackComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralStructuralSystemComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismFieldTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismFieldTransportCommonStage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismFieldTransportFiniteStage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismFieldTransportRationalScalar` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismPullbackRawStage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismPullbackTExactCoefficients` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IteratedReturnTransportData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.IteratedReturnTransportScalarCalculus` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedCommonEvaluationForStructure` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedCommonEvaluationNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedCompletedOperationModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedCompletionRealization` | unclaimed in shared mirror | Named normalization predicate or unchanged strict-tower notation; no application needs adaptation. |
| `Sheaf.Paper.NormalizedIntegralGeometricCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedIntegralMixedCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedIntegralScalarCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.OrdinaryDerivedProductLegTransposes` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PbcConstantWeilTwist` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PbcWeilCoefficientComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionReindexCoefficientTransition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionReindexCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionReindexModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionReindexShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionReindexSubstitution` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionTensorModels` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCompletionTensorNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodNormalizedTensorSignedShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingCompletionNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingCompletionUnitTensor` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingDerivedComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingGoodComplex` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingRestrictedTower` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingRoosShiftCompatibility` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingSignedRoosShift` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingStrictComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingTensorCoefficientTransition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingTensorConstruction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingTensorFamilyCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingTensorSignedShifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PodReindexingTensorSubstitution` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointAutomorphismDerivedTransportInverse` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointEquivariantCommonStage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointEquivariantDiagramData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointEquivariantDiagramLift` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointEquivariantFiniteScalar` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointEquivariantOriginalDiagram` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointExactDerivedModel` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartExactness` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartFiniteStage` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartFiniteStageData` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartFiniteStageEquivalences` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartFiniteStageScalars` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointHeartFiniteStageTruncations` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointInverseImageCoefficientTower` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointRealizationStandardCohomology` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointScalarCompatibleTransportTransfer` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointScalarSingleStepCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PointWeilFiniteStageDescent` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ProperFiniteNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RationalPullbackFibreComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RationalRestrictionComparisonCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RationalScalarSingleStepNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RealizedPullbackComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.RegularCoefficientCoherentReduction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ReindexingSystemHomReductionSquare` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ReturnScalarSquares` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.SfFrameworkThetaShiftCompatibility` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.SimultaneousIntegralPullbackComparisons` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.Paper.ZlFiniteIntegralFibreReconstruction` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransportQbarNaturalTransformation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.SixFunctors.FrobeniusPointTransportRationalScalar` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | unclaimed in shared mirror | Named normalization predicate or unchanged strict-tower notation; no application needs adaptation. |
| `Sheaf.TraceFormula.IsomorphismQuotientRoosComparison` | unclaimed in shared mirror | Named normalization predicate or unchanged strict-tower notation; no application needs adaptation. |
| `Sheaf.TraceFormula.IsomorphismRoosUnitCancellation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientModels` | unclaimed in shared mirror | Corrected auxiliary predicate; six other constructions unchanged. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientMultiplication` | unclaimed in shared mirror | Named normalization predicate or unchanged strict-tower notation; no application needs adaptation. |
| `Sheaf.TraceFormula.PointExactRealization` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.TraceFormula.StrictQuotientCompletionRealization` | P4 | P4 item: construction and naturality proof for corrected normalization. |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed in shared mirror | Supply canonical presentation coherence; theorem signature unchanged. |
| `Sheaf.TraceFormula.StrictQuotientConeAugmentation` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed in shared mirror | Transitive importer; no textual use of the changed predicate. Other definitions and instances unchanged. |

## Status

landed 20261026T130628-L-3484579 2026-10-26 (merge of deliver/P4/Sheaf.TraceFormula.StrictQuotientCompletionRealization)
