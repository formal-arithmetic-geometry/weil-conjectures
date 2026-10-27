# effectiveCompletionPresentationModels / IsEffectiveComparisonCompletionNormalized

## Reason

The original completion-only assertion has the same false universal presentation
quantifier already corrected in `coord/changes/P4-strict-completion-presentation-coherence.md`
and `coord/changes/S9-pullback-presentation-coherence.md`.
`CoefficientReductionPresentation` constrains the derived presentation isomorphism
only after finite derived evaluations. Conservativity does not imply faithfulness.
The planned `TrfCompletionRoosNormalized` argument already requires the missing
`IsIntegralComparisonPresentationCoherent` condition.

For the reviewed algebraic test, let A = Z_p, B the p-adic completion of a countable
free A-module, D = product_i A, and embed B in D by b_i -> p^i b_i. Set M = coker(B -> D).
Both B and D are torsion-free and complete, so M is derived complete. The class x
of (p^i)_i is nonzero, since its preimage (1)_i is not in B, but belongs to every p^n M:
subtract the first n coordinates. The nonzero square-zero map delta on A direct-sum M
sending 1 to x and vanishing on M has zero derived reductions. Indeed its source A/p^n
is free over the quotient ring and its class in H^0(M tensor^L A/p^n) is zero.
Thus 1+delta is an automorphism invisible at every finite derived evaluation but
detected by completion. On a flat-term K-flat representative it twists e without
changing kappa or the old finite presentation equations. The prescribed unshifted
sections and zero shifted coordinate fix v, so the two purported unit identities
would force completion to kill this nonzero twist. This reproduces the prior
reviewed mathematical obstruction; it is not a Lean-certified negation.

The correction requires the existing whole-system adjunction coherence, which
pins e as the derived transpose of the strict tensor-unit map. It is an explicit
correction of an auxiliary statement and definition, not a proof of the old false
assertion. All output coordinates and the entire derived-morphism equation remain
verbatim. `coherentPrimitiveReductionPresentation` gives such a presentation for
every good complex without boundedness, completeness or extra geometric hypotheses.
The zero complex, empty scheme, identity and exponent-one quotient use the same laws.

No Challenge theorem or definition used in its statement is changed. No source-library
file is edited. Coefficient objects, good complexes, derived operations, units,
transitions and the fixed Roos comparison retain their constructions and meanings.
The comparison proof interfaces and statements which quantify over them acquire the
coherent-presentation interpretation explicitly recorded in their DAG corrections.
The blueprint unit route is retained; only the identity-isomorphism detour below
this completion node is replaced by the existing strict completion realization.

## Old

```lean
theorem effectiveCompletionPresentationModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (ρ : IntegralComparisonRoosModel l E X),
    ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v
```

```lean
def IsEffectiveComparisonCompletionNormalized (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v
```

## New

```lean
theorem effectiveCompletionPresentationModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (ρ : IntegralComparisonRoosModel l E X),
    ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v
```

```lean
def IsEffectiveComparisonCompletionNormalized (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v
```

The theorem is proved by transporting the real strict quotient augmentation through
the inverse strict tower isomorphism. The existing private Roos coordinate and
restriction/evaluation lemmas compute its section maps and zero shifted coordinate.
Postcomposition by the forward tower isomorphism reduces its derived identity to
`strictQuotientCompletionUnit`. No hole is moved to another declaration.

The assigned module also adds proof-only imports of the canonical model, direct
strict completion realization, strict-unit private API, existing private normalized
Roos model, diagonal Roos coordinate helper and restriction/evaluation cast helper.
Its added `attribute [local irreducible]` command names only large existing coefficient,
constant-sheaf, derived-category, tensor, limit, restriction and evaluation constructions.
It controls elaboration inside this proof module and exports no attribute or instance
change. The corrected theorem compiled cleanly in 29.8 seconds in the initial check.
The combined compile then accepted all six files: the item, repaired parent,
adapted private consumer and three unchanged direct importers. Profiler totals for
the item were 14.1 seconds of tactic execution, 9.93 seconds of type checking and
425 milliseconds of serialization. Reported per-module wrapper/cache time is not
the Lean subprocess acceptance time; the service accepted each file under its
60-second Lean limit. Profiling options and validation-only copies are removed
from the delivery.

## Users

The only direct importer of the assigned item is the parent
`Sheaf.Paper.EffectiveComparisonRealizationModels`. Its definition receives the same
coherence arrow; its model-existence proof then uses the corrected item verbatim.
The only downstream textual use of that predicate or `completion_normalization`
field is the private `completion_normalized` helper in
`Sheaf.Paper.PodCounitScalarWordCoordinates`. It transports the coherence premise
along `leftAdjointUniq`, using `Adjunction.unit_leftAdjointUniq_hom_app`. Its public
signatures and visibility remain verbatim. Neither adapted module has a claim file
in the shared claim snapshot. The complete downstream list from `downstream.py`
is given below, including indirect consumers; there are no other textual field uses.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenRefinementAlphaPlusInclusion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.FiniteStageFibreVanishing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.GeometricCurveDiagramDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.MarkedGeometricCurveModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.OrdinarySectionScalarComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.PairEigenvalueCurveTest` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicStrataBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.FourierTransform.FourierDeligneTransform` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicActualSystemsNormalized` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicClosureScalarCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCommonStageFibreTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCommonStageFibreZeroMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCommonStageHeartExactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicCompletedTensorRealizationDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicExceptionalShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFiniteConstructibilityComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFiniteRealizationCocone` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFiniteRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicFiniteScalarCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreCommonStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreCommonStageData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreExactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibrePullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPullbackRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPuritySystems` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicProperOrdinaryPushPreservation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensorComponents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceFiniteness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceTransitionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicPurityTwistRestrictionComponents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicRealizationFamilyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicRealizationIsomorphismNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicReindexingCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicReindexingFunctoriality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicReindexingHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicReindexingTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicStratifiedPullbackInterface` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicTraceTensorShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdmissibleCupCoefficientPassages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineCoefficientCounitNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineCounitMateUnitChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalDncCoordinateIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalDncNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalIntegrationConstructions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalIntegrationOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalPowerCoefficient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalPresentedBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalRawTransposePower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalRestrictedTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalSectionCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalTraceRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineDiagonalTransposePower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineIntegrationExponentTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLineComparisonNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLineCompositeTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineLineStandingTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedCounitData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedCounitDescentComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedCounitSuccessor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedCounitZero` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedEvaluationContraction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedFirstLineCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationSuccessor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineOrderedTransposeCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceCoordinateBoundaries` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityCompositionMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityCoordinateInvariance` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityOrderedBlocks` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceThomMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceContractionProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceProductData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceSuccessorContraction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceZeroSectionConstructions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineTargetDiagonalDnc` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AffineVectorTracePresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.AutomorphismSquareRationalScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BarrettIndRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BasicOperationCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BasicOperationReductionAndEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryComparisonCompositionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteEvaluationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteSiteData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteSiteRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteTorDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.BoundedSiteExchangeTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateCommonComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateCompletedComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateComplexComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateNaturalityLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateOrdinaryNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateScalarComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CanonicalTateScalarNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CartierRelativeKummerRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CartierSupportedComparisonSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CentredDiagonalSourcePasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDiagonalAssemblyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDncNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDncSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDncVectorFactorData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartEpsilonPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartExceptionalCounitEquation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartIntegrationAdjoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartNormalIntegrationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalFiltrationDiagramFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalFiltrationExactDiagram` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalFrontierExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLocalFrobeniusData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseFiniteConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseFiniteOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseScalarCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRealizationLocalSpectrum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRealizationPunctualPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalRealizedAnchorEigenvalue` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalSuccessiveRestrictions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalSystemRawLisseRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreCommonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreScalarData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilCoherentDiagramStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationTransportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiniteDiagramDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClassicalWeilRestrictionExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenCanonicalFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenCanonicalRestrictionEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenCompletedTowerRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenCounitAdjointComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenExceptionalScalarDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenPrescribedWeilFiltration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenSystemFiniteRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenSystemIntegralRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenSystemRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClopenSystemRestrictionEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClosedCoefficientTransposeCocycles` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClosedEmbeddingPerfectEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClosedScalarDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ClosedSupportExceptionalMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CochainLocalizationTensorIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefSupportOpenTensorModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefSupportPointSectionsComparisonExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefSupportPointSectionsData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefSupportPointSectionsModelExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefficientEvaluationNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoefficientMapGeometricSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonConstantUnitFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonFrobeniusSquareNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionCompactificationOnStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionComparisonEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionCompositionOnStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenFactor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | J7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionProperFactor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionProperOnStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionProperTensorCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | J8 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionTensorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonProjectionTensorCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageOpenHeartAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStagePerfectEvaluationDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStagePointReturn` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactExchangeOperationCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportArrowScalarTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientExchangeInvertible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCompletedProjectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCompletedScalarArrow` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCompositeTransposeDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | G2 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealizationSetup` | F3 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportExchangeDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteScalarMateNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedScalarDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportPathReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoefficientChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoherenceLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFieldStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFiniteStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionIntegralStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionRealizationLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionRightUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizedScalarTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarEvaluationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarGammaIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarLimitFoundations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarLimitReduction` | D4 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarShiftNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarShiftStructures` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarShiftWitness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportStageActionAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | B4 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarRefinement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemTransposeNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportTermHomFinite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactSupportTotalLimitRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationBOrdinaryProjectionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationFiniteProjectionModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactificationStrictRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ComparedSmoothExchangeComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ComparisonImageClosedSectionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ComparisonPullbackRestrictionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompleteIntegralConstantRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompleteProjectionDescentMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompleteProjectionMateDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompleteProjectionReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedConstantRightUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedContinuousHomHypotheses` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedLocalFibreComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedPullbackFractionDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedScalarAssociatorLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedScalarExactLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedScalarLocalizationBalancing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedScalarTransportCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositeProjectionCoefficients` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionIteratedMateExpansion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionSingleMatePresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CompositionTensorMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteOpenScalarTensorSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFactorizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteProperScalarTensorSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConcreteSupportScalarIsomorphism` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedCompositorRealization` | Z8 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalCounitRepresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRealizationProperties` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalSystemRecognition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedIntegralEndpoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedTateIntegralTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CondensedTateIntegralTowerData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantCompletedOrdinaryAssociativity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantCompletedScalarAssociativity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantDirectImageTowerRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCyclicSheetPartition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionPullbackReturnResidue` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionPullbackSheetComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnExactFunctor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnLocalOperators` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnLocalSpectra` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnTransportComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetGeometry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetTensorSplitting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantScalarTowerAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantScalarTowerMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantTwistCoefficientComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstantWeilStageCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositorData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalLeftRefinements` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalRefinementMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleLeftCompositorCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleRationalHomComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleRationalLeftRefinement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleRingLeftRefinement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleTensorComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ConstructibleWeilModelSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateAdjunctionComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateCartierBoundarySign` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateLineAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateLineAugmentationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateLineConjugateExponents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateLineCounitTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionArrows` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionProductRecursion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionProjectiveTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionSiteTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateSupportedProductRecursion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateTowerCompactTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateTowerExceptionalCompositors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateTowerNormalizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateTowerNormalizationFusion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateTowerNormalizationInduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoordinateZeroBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CtfCoefficientStageSelectors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveClassicalFiltrationPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveClassicalPullbackExists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveRestrictionFiltrationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.CurveRestrictionLocalPowers` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DerivedHomSubstitutionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DerivedTensorRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DerivedWeilOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineCounitRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineIntegrationSiteSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineRankZeroActual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineTraceCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineTraceMapAgreement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineTraceSiteComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalAffineTraceSiteData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalCounitComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncAffineModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncAssemblyGlobal` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncChartNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleBeta` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleDualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityLocalInverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityTwist` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleAlphaSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleFactorization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleInverseDeformation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleLocalityUnitChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleNormalEndpoint` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleNormalTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleRestrictedDualizingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleRhoUnitSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleSourceDualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleSourceEndpoint` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleSourceTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryChartLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationGluing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryOverlap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryRealizeRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationChartExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationRefinement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationRefinementData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DifferenceFirstInputRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DifferenceSecondInputRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DirectImageCoefficientExchangeInvertible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DirectImageLimitComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DirectImageScalarRealizationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DoubleDiagonalSectionIdentifications` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingCocycleSourceEtale` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingCompositionCoefficientMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingPrimitiveOpenRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingSigmaCocycleLocality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.DualizingUnitComposite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed in shared snapshot | Correct matching auxiliary predicate; assembly uses the item verbatim. |
| `Sheaf.Paper.EffectiveCompletionPresentationModels` | E1 (assigned item) | Correct false auxiliary presentation quantifier and prove its coherent version. |
| `Sheaf.Paper.EtaleCartesianTowerTensorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleCompositeEComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleMiddleTensorAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EtaleTensorSourceTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenLineBinaryProductNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenLineCoefficientProjectionNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenLineCoordinateIntertwining` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenLineProductIntegrationSymmetry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.EvenTateLineSelfSymmetry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExactProperOpenProjectionMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalCommonStageFromRational` | K7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalDualizingBaseChangePasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFieldDescent` | A3 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFieldStageCompletion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteIntrinsicBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteScalarMates` | A4 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralAdjunctionLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralSupportAdjoint` | M5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRationalStageLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementLeftConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMatesData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementRightSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementSystemData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementSystemRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementTransportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRingScalarMates` | M7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRingStageAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalRingStageAssemblyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalScalarMateLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExchangeFunctoriality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdNormalizedPullbackGeometry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdNormalizedPullbackIntegralScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdNormalizedPullbackMixed` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed in shared snapshot | Direct importer; no use of the changed predicate or field; compile original. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdPullbackWeilReturnSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldCohomologyPerfectDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionCompletedStrictLimit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionLimitEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionReductionDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionReductionLimits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionSourceNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionStrictLimits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionSystemCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldExtensionTowers` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemFiniteOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemHeart` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemNormalizations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemRigidity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldOrientedExchangeSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldProjectionRefinementSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTransposeBase` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTransposeCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionCoefficientSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionIntegralComponent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionIntegralNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCanonicalComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCounitBijective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCounitFiniteFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPairData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportCoefficientSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportEvaluationRefinement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalBaseChangeReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalDncReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalOrientationAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalVectorReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalSiteNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFirstRootChart` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteForwardCompactifiedSwap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteForwardProductCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtensionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportSiteSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeProperScalarComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricOrientationExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricPurityCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricPurityFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricPurityMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteGeometricTensorExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteHorizontalShriekMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteIdentityCompositionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteIntrinsicProjectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteMateDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteOrientationScalarPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePartialPullbackTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePartialTensorIdentityComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePointCounitUnitNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePositiveChartFrameExt` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePositiveChartRecursion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePositiveRootChartPower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePositiveRootCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProductOpenRestrictionPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProductOrdinaryNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProductReductionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting` | S9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionBinarySquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` | T6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionCompactificationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionCompactificationTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | U6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionCompositionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionFromDescent` | M9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionIdentityNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionInputNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionIterationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | P5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionOperationPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionRefinementLeft` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProjectionTensorSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteProperProjectionTranspose` | P6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePublishedRootChartPower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FinitePuritySourceUnitReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteQuotientModuleBalancing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRationalHeartComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRealizationEtaleOrigin` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionBaseChangeSource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionExceptionalFiniteModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionLineChartScalars` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionLineInputConstructible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionPositiveLineComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionReassociation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionShiftedPullbackCube` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionSourceChartIndependence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionTensorSource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteReductionThetaFactor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRefinementAmbientNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRefinementProjectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionDiagramNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRootLinePowerTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteRootTensorPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteScalarCochainComparisonIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteScalarMonoidalRepresentative` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteScalarRepresentativeIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteScalarTensorData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteScalarTensorSource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSheafH0Augmentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSignedTwistProducts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSiteCounitProjectionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSiteTensorProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSourceChartPowerTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSourceChartScalarTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSupportFactorRealization` | U7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSupportOriginComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteSupportedReductionEquation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTargetChangeCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTateSourceMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTateSourceStructuralCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorComparisonEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorFixedComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorLineChartReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorLineDerivedExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorPresentationReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorProductFrameExt` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorProductMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorProductMapIsIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorPullbackCompositionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorPullbackTensorReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorSemilinearReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftFirst` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorShiftSecond` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorSignedReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTensorSymmetryCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTripleProductDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTripleProductNormalForms` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteTypeCoordinateSupportOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FixProjectionCompactificationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FixedPresentationUniformizerReductions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ForwardProductCoordinateTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcIntegralComparisonLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactIntegralNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactRationalNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.FrobeniusWitnessedCompactification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeneralChartComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricCommonStageDirectImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricScalarFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GeometricSmoothReconstructionSetup` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GermReparametrizationDerivedDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.HigherIdentityCompositionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.HigherTensorIdentityComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IdentificationCoefficientTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IdentityCoefficientTransportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IdentityCompactificationSystemMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IdentityOpenSystemEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralAutomorphismCancellationNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralClosedSupportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCoefficientModelComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | P7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCompositionCoefficientSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralDatumPullCompositionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralDualizingExceptionalUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricPurityRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricReindexingRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricSupportRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralGeometricTransposeIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralLissePullbackNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenAdjunctionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenEmptyPullbackVanishing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenProjectionCoefficientData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenPullTensorReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOpenSupportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOrientationShiftedSheafModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralOrientedExchangeSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionCoordinateData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionDirectFactorEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionEvaluationFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFactorData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFactorEvaluationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionLocalFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionMiddleMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOpenFactorEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOpenFactorReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOpenTensorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOperationPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionProperFactorReduction` | P9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionPullEvaluation` | Q5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionReductionCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionReductionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionRefinementSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSupportEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSupportFactorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSystemCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSystemEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProjectionTensorEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProperOperationProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionCoefficientData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionSystemNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProperSupportReductionIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralProperTensorPullbackReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPurityComparisonCocycles` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralPurityCounitReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralQuotientCohomologicalBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralReductionJointFaithfulness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralReductionShiftedHomFiniteAlgClosed` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralReductionShiftedHomFiniteQcqs` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSectionsPerfectReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSemilinearGermSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralStageProjectionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralStageProjectionStructuralIdentities` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSupportFunctorNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSupportNormalizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralSupportReductionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegralTowerProjectionMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegrationAffineExponentTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegrationCoefficientProjectionNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegrationExponentTransposeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegrationExponentTransposeTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntegrationProjectiveExponentSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntrinsicConstructibleFibreExactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IntrinsicLocalLatticeComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportCommonStage` | Q9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportFiniteStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportRationalScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismFiniteExchangeCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IteratedPurityScalarPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IteratedTateSourceComposite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.KummerSiteCohomologyNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LineCounitComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LineKummerFieldRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LineZeroClassExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeChoiceExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeHeartLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeHeartLiftData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeLisseDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeNormalizedRealizations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeRealizationFaithful` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseLatticeSingleComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LissePointSectionsRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseTensorPullbackRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LisseTensorPullbackRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeCoefficients` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeScalarTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeTransportAddition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeTransportNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeWeilAddition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusStepCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocallyClosedRelativeTransposeNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | G6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.LocallyFiniteCompactSupportStageAction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCompactSupportExchangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupNormalizedScalars` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupOperationComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupTensorComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelAffineIntegrationOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelChartOrientationAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelOrientationChartDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelOrientationSourceNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ModelOrientationTateDetection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeAdicCompactSupportSums` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeAdicFiniteNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeAdicRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeAdicReindexingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeAdicTensorReindexing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeCoefficientInverseImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | G8 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeCompactSupportGeometry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeConstantSupportModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeDirectImageSections` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeProperTensorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeReductionCounitKFlat` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilComparisonStructure` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilDerivedInductionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilDualizingHomTransposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilFreeCoproduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilHeartProperties` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilInductionComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilInductionSummands` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilProperNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalModelSectionOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalSectionIntegrationBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalSectionIntegrationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalSectionIntegrationOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedCommonCoefficientLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedEtaleComparisonComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedEtaleRestrictionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTraceCommonStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTraceData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedHeartRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralTraceData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedLatticeFiniteFree` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackObjects` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedRationalLeftComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedRationalLeftIdentity` | X9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedRationalLeftLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedRingRefinementLaws` | H7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedScalarAssociatorLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedSmoothOrientationUnits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedStageCoefficientCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedSupportEtalePresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedTateTensorTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedTateTensorTowerCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedTateTensorTowerProperties` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.NormalizedTateTensorTowerZero` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenProjectionFactorCoefficientChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenProjectionFactorCompositorTransport` | S6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenProjectionIsoCoefficientChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenWeilCarrierRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenWeilCoefficientFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenWeilFiniteStageFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenWeilGeometricFibres` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OpenWeilPunctualSpectrum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OperationCoefficientActionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OperationScalarTransportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedAffineComparisonNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedAffineLineTransposeNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeSuccessor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedIntegrationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedLineLevelBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedTateTowerCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrdinaryOpenScalarComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrdinaryScalarBalancingLevel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrdinaryScalarReductionGenerators` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationCoordinateBoundaryPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationCoordinateModelBoundary` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationEtaleCoefficientTwists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationFiniteCoefficientTwists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationFiniteReductionTwists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationGeometricComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationLocalResidue` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationPerfectLines` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationScalarPropagation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientationScalarTowerTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientedDoubleHomCancellation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.OriginalScalarMateShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PairingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PbcConstantWeilTwist` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PbcWeilCoefficientComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PerAdicNormalizedFibreComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PerfectDualPairAndTateStability` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PfReductionProperOpenIdentities` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed in shared snapshot | Transport the new coherence premise in one private proof; public signatures unchanged. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodMixedSupportCupProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodReconstructionCommonStageCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodReconstructionCommonStageData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodReconstructionRawRationalNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PodReconstructionScalarRealizations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PoincareDualityConventions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointFiniteMultiplicationInverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointFrobeniusNormalizationDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointIdentityExchangeRecipe` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointPowerRoosComparisonSpecialization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointPowerStrictInsertionSpecialization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointPullbackConeLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointQuotientComparisonCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointQuotientTowerCoherentSource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointQuotientTowerData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointQuotientTowerHomotopy` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointRealizationStandardCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointReductionAugmentationComplete` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointRestrictionWholeRoosSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointScalarPunctualSpectrum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemInsertionComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemInsertionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemNormalizedComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemNormalizedComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemRoosComparisonAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemRoosRestrictionAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransportData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransportRepresentative` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemStrictInsertions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportResolutionCancellation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotientAllComplexes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotientIdentities` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotientSections` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportTowerRealizationAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportTowerRealizationConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportTowerRealizationIdentities` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointTransportTowerRealizationSpec` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilAlgebraicFlag` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilHeartFlagData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilPairingCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilTensorRepresentatives` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PointWeilTransportUnitShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleAffineLineCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleFrameIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleOrderedIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectiveCoefficient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleVectorIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProEtaleVectorIntegrationArrows` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductCompositionCoordinateComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductExchangeCoordinateDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductExchangeCounitCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductHorizontalExchangeFactorization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductOpenAdjunctionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductOpenCounitNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductOpenSupportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionCompactificationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFactorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization` | T5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityProperCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityPullbackUnits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityTensorUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionMateFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionPurityCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionReductionPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionReductionWitnessedFlatDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionScalarSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionTensorActionExpansion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientCocycles` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionTensorIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionUnitIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionUnitPresentationNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperBiproductCoordinate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCoefficientDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCoefficientDescentData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCompactCoefficientActionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCompactIntegralComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperCompactRationalFunctorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperIntegralScalarSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperIntegralTowerComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperRationalScalarSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperSupportCoefficientAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperSupportFiniteAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperSystemEvaluationTransitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ProperWeilIterateGermFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PulledOrderedLineSingle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurCoordinateRepresentingFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPairData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportDerivedComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportOrdinaryComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurSupportPresentationAlpha` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineChartExceptionalIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineBoundaryRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityCompactSupportTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityCompositionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityCompositionCompatibleDncCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityConstantFamilyBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityKappaStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityKummerTriangleConcentration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityOrientationDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityPullbackReductionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityRankZeroFamilyReadings` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionBaseComparisonLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionConstantTrivialization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionEtaleRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionFibreSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionNormalizedSpecialization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityTateDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityTowerReductionComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityWitnessedMateNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.PurityWitnessedOpenChartTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportFiniteComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportFiniteMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportImageComplete` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportNormalizedLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportOpenComplete` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportProperComplete` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportReductionRigidity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportStrictReductionGamma` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` | E4 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QuotientGermTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.QuotientStalkNaturalDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RamifiedImageBalancingEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RamifiedQuotientSectionPushout` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalAmbientPullComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalAmbientPullModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalBalancedFreePullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalContinuousFiltrationModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalContinuousPullbackTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalCoverReflectsIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalEvaluationCover` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalOrdinaryCohomologyTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalProjectionComparisonEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalProjectionTensorCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalProjectionTensorModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPullSingleComputation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPullbackCompositionCoherence` | K9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPullbackFlatComputationCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityCoefficientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityCompactLattices` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityCompactScalarInvertible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpointData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityExchangeEndpoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityFiniteAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityIdentityDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityLocalizedFamilyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalPurityTwistedExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationFiniteConeModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationHomTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationOrdinaryLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalReturnBlockPower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarBalancedLocalization` | M5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarCompletionUnitSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarMixedUnitCancellation` | G3 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalStratumPullbackData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalStratumPullbackModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalizationOrientedExchangeSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RealWeights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedBrownMateLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementCommon` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementSingleDegree` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementTraceSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementTraceTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RefinementFiniteOriginEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeKummerSiteNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeKunnethClosedFibre` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeKunnethConstructions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductCoefficientFactorSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductFactorSquaresCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeProductProperCompatibilityCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalDncTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalSectionTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalVectorIntegration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RetaggingCoordinateOrientations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RingOpenRefinement` | T8 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.RingRefinementScalarWord` | T9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SbcDatumExchangeComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarComplexAdjunctionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarFibreCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarFibreComponentData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarFibreComponents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarFibreNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarHomPresentationEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitConstraintShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitRestrictionKInjective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitRestrictionLimits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitTensorComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitTensorKInjective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarLimitTensorRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientComplexNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientModuleTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientTotalTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarPullTensorCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarReductionTowerBalancing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarRefinementOriginsE` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarRefinementOriginsF` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarRestrictionComplexNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarRoosComparisonUnique` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarSourceCounitUniversal` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ScalarTargetCounitUniversal` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SectionDncIntegrationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SectionEtaleOpenCancellation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SectionsRationalModelComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearCommonOrdinaryCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearCommonRefinementCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearCommonSupportCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeCubeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeDescentData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearGermIterationDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearRationalOrdinaryCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearRationalRefinementCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SemilinearRationalSupportCubes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfAdicCommonStageDescentEquivalence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfBcCompletedMateDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfCompletedExchangeTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfFieldMateDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfIntegralLocalizationConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalClosedComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalWeilSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageBaseChangeDomainRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageCommonStageTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageIntegralRecollementNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageIntegralRecollementSource` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageIntegralSupportTowerNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationBoundaryData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationBoundaryDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationRationalTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfPositiveFiniteLocalizationConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationCommonStage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationExactDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationFiniteCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationFiniteData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfRationalLocalizationOrthogonality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ShiftedCoefficientLinesInvertible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorMixedSupportCupProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationStageCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothExceptionalTensorPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothExchangeScalarCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOrientationCoefficientFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOrientationPuritySquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOrientationStageExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOrientationTransportSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothOrientedExchangeComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityTensorUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SourceSectionAutomorphismModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SourceSectionIdentityModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SourceSectionRestrictionModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SpecifiedIntegralUnitOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SpecifiedTowerAdjunctionCharts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictCoefficientOpenReduction` | V7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictCoefficientProperReduction` | V8 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictDirectImageMixedUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictDirectImageMixedUnitData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictMixedFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictMixedScalarSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictMixedSystemModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictProperBiproductCoordinate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictProperCompositionRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictProperRestrictionComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictQuotientStalkReindexing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictReductionCompactSupportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictRefinementRestrictionSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictRefinementSeedRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarFiniteEvaluationTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarMateEvaluationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarMateFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarMateShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarOpenComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarOpenUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarProperComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarPullComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.StrictScalarTowerAssociator` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SupportedCartierDerivedPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SupportedProjectiveChern` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SupportedProjectiveChernComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemCompactSupportRestrictionCocycle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemCompositorRefinementSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemIdentityOpenEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | Y6 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemProjectionChangeCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemProperIdentityOpenProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemRefinementFiniteCoordinates` | V9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemScalarBasisDistributivity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemScalarRefinementRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemScalarTensorConstituents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationCoreExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.SystemTensorSemilinearRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorExchangeCtfDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorHeartSpecialization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorMateBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TensorTransposeTowerNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerFactorOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerFactorTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerIsomorphismPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerMuEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerNormalizationPreservation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerOrientationEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerOrientationWordNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerPurityAdjointTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerPurityPresentationRetagging` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerSemilinearPurityFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTateSplitNormalized` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTensorPresentationRetagging` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTraceCanonicalIntegral` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTraceOrientationUniqueness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TowerTraceScalarCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceStalkTowerDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TraceStrictStalkTowers` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportCondensedStageRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralBaseChangeRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralChartRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralCompositionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TransportIntegralStageConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCartier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionProjective` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionSign` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCofinalModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackLineMembership` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionTower` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTateReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerOrigins` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.UniformTowerTensorClosure` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VaryingDimensionDualizingInverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleFrameOrientationRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorFrameIntegrationSiteDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationChartTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationIdentityAdjunct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorIntegrationUnitTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorNormalizedTraceCartesian` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorTensorOrdinaryNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorTensorProjectionComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorTensorSiteEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VectorZeroSectionIntegrationBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierCompositionMateNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierIdentityProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierPairingThreeTransposes` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilGenericLissity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilGeometricFiberProperties` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndOpenRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndOpenRepresentability` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndProperHigherRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndProperHigherRepresentability` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndProperOpenHigher` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilPullbackFibreReturn` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlImmersionFilteredReductionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlImmersionRestrictionAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlOpenCompactSupportRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlOpenExtensionAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlOpenExtensionTExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlWeilPullCompositorEquivariance` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingExponent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineChartFormulas` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityLineComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionOrientation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientSystemBetaLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientSystemClopenLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CanonicalShiftSynchronization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CartesianCandidateCompositor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CartesianCandidateSiteSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CartesianCompactSupportCompositor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CartesianTowerRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefDualizingSiteMates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefFinitePairingEvaluationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingCompactificationModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingFiniteNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingFrameNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingSystemDinaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierDualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierExceptional` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefScalarReductionExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefWeilExceptionalCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefWeilNormalizedDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefficientDualizingClosedDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefficientProjectionPointData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefficientUnitFiniteTor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CoefficientUnitNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompactifiedProperTowerExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedOpenCartesianIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeDomains` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangePaths` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedSystemPullbackPreservation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompletedTensorSlotShiftLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralSystemExistence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransitionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdierData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteCounitRestrictionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizingAffineRestriction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizingData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizingScalarRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalQuotientIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicBidualComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunctionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteOpenCartesianCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyCoefficientCocycle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicGeneratorSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalAmbientModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalRealizationSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalSystemCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralComparisonRecursionLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransportHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizingFiniteBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizingMappingLimit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizingRoosModel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalLimitConstructible` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalEquations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCoefficientSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionTransposeIsIso` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralFiniteProperMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralFinitePullbackCoordinates` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralFinitePullbackNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenFiniteEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenRealizationNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenScalarUnitSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | W9 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` | X5 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | X7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralProperFiniteProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportCounitProjection` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportProjectionTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportRealizationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportTowerNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemDualityCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemProperOpenTransport` | Y7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierSignedCalculus` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.KappaGeometricComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.KappaMixedCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCoefficient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCompletion` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateFinite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenExternalTensorNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherenceData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorExchangeRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorOpenRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorProjectionRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenNormalizedProductCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenScalarAdjunctionCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenSupportStepBounds` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryAmbientAlphaPasting` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryAmbientAlphaUnits` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryProperOpenInvertibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProductCompactificationIdentity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProductSystemUniformRealizationDomain` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementComparisons` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementInputs` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProjectionSystemCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | Z7 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemAmbientCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemTensorComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarPreparation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarSupportCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalHomIdentifications` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalOperationsData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierDatum` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeSingleShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeSystemSquare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionLocalTensor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionProperComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionWords` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SemilinearOpenExternalCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.StructuralReductionWordSubstitution` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenLambdaExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemTensorShiftCoherence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.SystemTotalEnrichedTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TensorExchangeCoherentConclusions` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TensorExchangeNormalizedModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TensorExchangePresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TensorHomTranspositionData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.ThreeCellCompositor` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionNormalForm` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.VerdierExchangeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryProductTransposeData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleLeftComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleProductTranspose` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleRightComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.TraceFormula.CompactDirectPowerTransportNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | unclaimed in shared snapshot | Direct importer; no use of the changed predicate or field; compile original. |
| `Sheaf.TraceFormula.FrobeniusCompactPowerExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.TraceFormula.FrobeniusProperPowerExchange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.TraceFormula.LocalNormalizationStrictRealization` | unclaimed in shared snapshot | Direct importer; no use of the changed predicate or field; compile original. |
| `Sheaf.TraceFormula.PointConeLiftsChainNaturality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportBrownConstructibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetful` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetfulData` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalLeftModels` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalPointUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalStructuralTransport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.OrdinaryClosedPresentation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.WeilSheaf.StructuralOmegaHomPairs` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `TargetsCheck` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | C3 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.Statement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.Main` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.Product` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.Karoubian` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.KaroubianPointer` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | K3 | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed in shared snapshot | Transitive importer; no textual use of the changed predicate or field; no adaptation. |

## Status

landed 20261027T123432-L-2297458 2026-10-27 (merge of deliver/E1/Sheaf.Paper.EffectiveCompletionPresentationModels)
