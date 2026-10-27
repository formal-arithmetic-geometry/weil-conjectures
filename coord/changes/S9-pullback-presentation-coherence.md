# IsIntegralComparisonPullbackNormalized

## Reason

The original normalization quantified over e constrained only by finite derived
comparison equations. This is insufficient: derived evaluation is not faithful.
The existing parent module already marks this exact problem STATEMENT-DISPUTED;
T6 and S6 reports describe the obstruction rather than solve it.

For the algebraic test take A = Z_p, B the p-adic completion of a countable free
A-module, D = product_i A, and inject B into D by b_i -> p^i b_i. Its cokernel M
is derived p-complete. The class x of (p^i)_i is nonzero, since the would-be
preimage (1)_i is not in B, but x is in every p^n M: remove the first n coordinates
using a finitely supported element of B. On K=A direct-sum M the square-zero map
sending 1 to x and vanishing on M is nonzero, but vanishes after every derived
finite reduction (the source A/p^n is free in that coefficient category).
Thus 1+delta is an automorphism invisible at every finite level and visible to
derived completion. On a flat-term K-flat representative its reduction twists e
without changing the old presentation hypotheses or kappa. The strict generator
formula fixes q independently of this twist, whereas the limit equation changes.
This is the defect of the old universal quantifier; no finite detection argument
can repair its proof. The same test was recorded in the prior T6 report.

The corrected presentation pins e under two genuine adjunction Hom bijections
to the localization of the strict tensor-unit map specified by kappa. This map
is fixed on all sections. Both Hom bijections are injective, so e is fixed in the
whole derived category before taking a total limit. For the actual ordinary
quotient construction, the derived Hom formula gives this condition, so the
condition includes the canonical presentations of every good complex; it is not
an extra boundedness, completeness or geometric hypothesis. Zero complexes,
positive exponent one, the identity map, and empty sites use the same units.

This is an auxiliary definition correction. No theorem in Challenge.lean changes.
No coefficient ring, source module, pullback functor, derived category, good-class
predicate, or target-statement definition is edited. The natural realization and
its strict generator and Roos normalization equations are retained verbatim.
The scalar predicate and separately disputed completion-presentation assertions
are not repaired here and are not used by the new assembly.

## Old

```lean
def IsIntegralComparisonPullbackNormalized {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z)
    (realization : integralDerivedPullback l E f ≅ S.reduction ⋙
      integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj),
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E Z ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralDerivedPullbackComparison l E f).hom.app P
```

## New

```lean
@[irreducible] def IsIntegralComparisonPresentationCoherent
    (S : CoefficientDerivedSystemCalculus l E X)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P) : Prop :=
  ∃ b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C,
    (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((b.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E X (C.X i) n U
          (integralComparisonSequenceSection l E X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x)))) ∧
    (integralComparisonConstantTower l E X).map
        (S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
          (coefficientSequenceLimit l E X).map e.hom) ≫
        (integralComparisonTowerCounit l E X).app
          ((coefficientSequenceDerivedRestriction l E X).obj (DerivedCategory.Q.obj C)) =
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map b ≫
        (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.inv.app C

def IsIntegralComparisonPullbackNormalized {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z)
    (realization : integralDerivedPullback l E f ≅ S.reduction ⋙
      integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj),
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E Y S P.obj C e κ →
    ∃ q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E Z ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralDerivedPullbackComparison l E f).hom.app P
```

The existing integralComparisonLimitToRoos definition is also given its explicit
return type (the same complex hom type Lean previously inferred). Its construction
is unchanged. This is an elaboration optimization, not a mathematical repair.
The item node's incomplete introductory clause is completed to its existing Lean
existence signature; its own statement_change audits the parent.

The same file's Roos field is factored through a named proposition to avoid
repeating the long derived-limit equation in structure elaboration. This is a
pure definitional abbreviation: unfolding IsIntegralComparisonRoosNormalized
recovers the original field type verbatim, so no consumer's mathematical
statement changes and no consumer adaptation is needed. The existing
IntegralComparisonRoosModel constructor and projections keep their names.

Original Roos structure:

```lean
structure IntegralComparisonRoosModel where
  /-- A natural comparison on entire strict tower complexes. -/
  comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  /-- It is induced on simultaneous K-injectives by the ordinary limit cone. -/
  computes : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
      [I.IsKInjective],
    comparison.hom.app I =
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I)
```

Factored Roos normalization and structure:

```lean
def IsIntegralComparisonRoosNormalized
    (comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) [I.IsKInjective],
    comparison.hom.app I =
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I)

/-- The Roos model of total limit, with its exact K-injective normalization.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonRoosModel where
  /-- A natural comparison on entire strict tower complexes. -/
  comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  /-- It is induced on simultaneous K-injectives by the ordinary limit cone. -/
  computes : IsIntegralComparisonRoosNormalized l E X comparison
```

## Users

The downstream.py --uses audit found two users of the pullback predicate and
thirteen of its model type, fourteen distinct modules. The purely definitional
Roos-field factor has thirty-one direct users; the table includes their union. No existing complete proof applies
that predicate with the old number of arguments. The remaining direct uses are
fields, hypotheses, aliases, or statements whose proofs are still open. The
realization field is unchanged. A canonical coherent quotient presentation is
sufficient for the uniqueness, shift, counit and composition arguments; their
strict tensor-unit tests still pin the same mathematical maps. The DAG
statement_change records all 51 original citers. Three further DAG citers have no current source file and no row in rework.tsv:
AdicExceptionalCompositorCoefficientsData, NormalizedScalarComparisonRealization,
and IntegralPullbackCounitProjection. Their recorded mathematical statements use
the same canonical operations and remain applicable; their absent Lean bodies
could not be inspected and are not withdrawn or altered.
The new split nodes are also
consumers and explicitly require the corrected predicate.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Repaired predicate; existing constructions and complete proofs retained. |
| Sheaf.Paper.PodCompletionReindexModels | unclaimed | Alias PullbackNormalization inherits corrected predicate; no application proof needs adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.EffectiveQuotientModelDescent | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.IntegralComparisonPullbackRealizationShifts | unclaimed | Signature unchanged; canonical coherent presentations and their shifts replace the arbitrary chosen presentation in its proof plan. No code edited. |
| Sheaf.Paper.IntegralComparisonSystemData | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.PrimitiveQuotientPullbackModelExistence | S9 | Constructed the corrected model from two strict substeps and existing descent. |
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.PrimitiveQuotientRealizationsUnique | P5 | Signature unchanged; proof must choose an adjunction-coherent canonical presentation. No code edited. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | No code adaptation: uses the canonical normalized model as data; mathematical operation unchanged. |
| Sheaf.Paper.CoherentQuotientReductionComparison | S9 (new) | Requires whole-system coherence and identifies the derived comparison before any limit. |
| Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison | S9 (new) | Uses only the unchanged ordinary generators, not the repaired derived predicate. |

| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.EffectiveCompletionPresentationModels | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.IntegralComparisonScalarRealizationShifts | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.NormalizedCompletionRealization | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.PodCompletionReindexShifts | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.PodReindexingDerivedComparisons | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.PrimitiveQuotientScalarModelExistence | T5 | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | H7 | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | V2 | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.ScalarModelUnit | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | unclaimed | Roos field factor only: unfolding the named predicate recovers exactly its old type; no statement or proof adaptation. |
Consumers may require rechecking the canonical coherence in their unfinished
proofs. Their intended operations and equations are unchanged. In particular
PrimitiveQuotientRealizationsUnique is held by P5 and is not modified.



## Status

landed 20261026T071021-L-3770140 2026-10-26 (merge of deliver/S9/Sheaf.Paper.PrimitiveQuotientPullbackModelExistence)
