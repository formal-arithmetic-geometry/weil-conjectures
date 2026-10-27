# WeilConjectures.trfQuotientTowerFunctor and the strict quotient models

## Reason

The proof of multiplication-cone descent uses three independent strict-system
lemmas. They need the seven existing definitions in the item. Relocate those
definitions to `Sheaf.TraceFormula.IsomorphismStrictQuotientModels` and
publicly import that module from the item, so the smaller lemmas can be imported
without a cycle. The statements, universes, names, visibility and all seven bodies
are unchanged. Five former abbreviations use `@[reducible] def`: elaborator
reducibility is preserved, while ordinary kernel hints avoid eager expansion of
large complex, tower, difference and product-comparison constructions. No target,
source-library declaration or mathematical notion changes.

The comparison modules locally prefer the existing `integralTowerHasDerivedCategory`
instance at priority 3000, as does `IntegralOperationsWellDefined`. This keeps the
same standard localization presentation throughout the comparisons. The priority
change is local and exports no new instance priority.
In the item the priority attribute is confined to `section DescentProof` (reviewer fix,
2026-10-26), so the public theorem `isomorphismMultiplicationConeDescent` elaborates
its unchanged statement with the published instances
(`integralOperationsCommHasDerivedCategory` on X), as before the delivery.

The common module keeps three direct public imports. Its other five former direct
imports are publicly supplied by those three; the assigned module retains every
original public import. Comparison statements use matching local transparency
settings, keeping the completed commutative-ring presentation and `sheafCompose`
implicit-reducible while abstracting the recorded derived constructions. These
attributes are local and preserve every mathematical value.

## Old

In `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent`:

```lean
/-- The actual strict quotient tower D, functorial in the original complex.
Source: blueprint rational-frobenius-integral-model (2); Stacks 06YY and 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
def trfQuotientTowerFunctor (W : Scheme.{t}) :
    CochainComplex (integralTowerModules l E W) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

/-- Termwise completed inverse image, with scalar action through c inverse.
Source: blueprint rational-frobenius-integral-model (2); Stacks 03D6
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseImageComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Postcomposition on strict towers, retaining their transition maps.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseImageTower {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (Functor.whiskeringRight ℕᵒᵖ
    (CochainComplex (integralTowerModules l E Y) ℤ)
    (CochainComplex (integralTowerModules l E X) ℤ)).obj (trfInverseImageComplex l E g)

/-- The existing difference 1-s on the product of the quotient tower D(Q).
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfQuotientDifference (W : Scheme.{t})
    (Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E W).obj Q).obj (op n))
    (integralOperationsTowerStep ((trfQuotientTowerFunctor l E W).obj Q))

/-- The same difference on GD(Q), with the actual inverse-image transitions.
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseQuotientDifference {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfInverseImageTower l E g).obj
      ((trfQuotientTowerFunctor l E Y).obj Q)).obj (op n))
    (integralOperationsTowerStep
      ((trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj Q)))

/-- The canonical product arrow phi, characterized by its product projections.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfQuotientProductComparison {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  piComparison (trfInverseImageComplex l E g)
    (fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj Q).obj (op n))

attribute [local irreducible] integralOperationsRoos

/-- The normalized representative comparison for L R. It tests whole strict quotient
presentations, not only their derived evaluations. The section formula fixes the
strict tower identification a to the actual finite comparison kappa. The final
formula is its total-limit/Roos realization, including the specified comparison e.
Source: blueprint rational-frobenius-integral-model (2)--(3); Stacks 06YY and 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
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

attribute [local semireducible] integralOperationsRoos
```

## New

The complete relocated declaration bodies are:

```lean
def trfQuotientTowerFunctor (W : Scheme.{t}) :
    CochainComplex (integralTowerModules l E W) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

/-- Termwise completed inverse image, with scalar action through c inverse.
Source: blueprint rational-frobenius-integral-model (2); Stacks 03D6
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseImageComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Postcomposition on strict towers, retaining their transition maps.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseImageTower {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (Functor.whiskeringRight ℕᵒᵖ
    (CochainComplex (integralTowerModules l E Y) ℤ)
    (CochainComplex (integralTowerModules l E X) ℤ)).obj (trfInverseImageComplex l E g)

/-- The existing difference 1-s on the product of the quotient tower D(Q).
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfQuotientDifference (W : Scheme.{t})
    (Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E W).obj Q).obj (op n))
    (integralOperationsTowerStep ((trfQuotientTowerFunctor l E W).obj Q))

/-- The same difference on GD(Q), with the actual inverse-image transitions.
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseQuotientDifference {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfInverseImageTower l E g).obj
      ((trfQuotientTowerFunctor l E Y).obj Q)).obj (op n))
    (integralOperationsTowerStep
      ((trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj Q)))

/-- The canonical product arrow phi, characterized by its product projections.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfQuotientProductComparison {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  piComparison (trfInverseImageComplex l E g)
    (fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj Q).obj (op n))

attribute [local irreducible] integralOperationsRoos

/-- The normalized representative comparison for L R. It tests whole strict quotient
presentations, not only their derived evaluations. The section formula fixes the
strict tower identification a to the actual finite comparison kappa. The final
formula is its total-limit/Roos realization, including the specified comparison e.
Source: blueprint rational-frobenius-integral-model (2)--(3); Stacks 06YY and 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
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

attribute [local semireducible] integralOperationsRoos
```

The definitions above, with their exact types and terms, now occur in
`Sheaf.TraceFormula.IsomorphismStrictQuotientModels`. The declarations
`trfInverseImageComplex`, `trfInverseImageTower`, `trfQuotientDifference`,
`trfInverseQuotientDifference` and `trfQuotientProductComparison` use
`@[reducible] def` in place of `abbrev`. This preserves their elaborator
reducibility and mathematical values, with ordinary kernel unfolding hints. The original module adds:

```lean
public import Sheaf.TraceFormula.IsomorphismStrictQuotientModels
```

The documentation's blueprint tags attach the moved definitions to the new
definition node. The new module keeps the existing public dependency imports.
Consumers continue to receive exactly the same definitions through the item.
The item removes four unused proof-only imports; it imports the three strict
comparison modules privately. Its eight previous public imports remain verbatim.

## Users

The downstream check was run for all seven relocated names. It found the following
textual consumers. Each still sees the identical declaration and term through the
public re-export, so no consumer adaptation is needed. Other transitive importers
retain the same public API. No consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.NormalizedCompletionRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointFrobeniusNormalizationDefinitions` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointQuotientComparisonCoordinates` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | V2 | Retains its statement; its proof uses the normalized record and re-exported models. |
| `Sheaf.TraceFormula.IsomorphismQuotientRoosComparison` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismRoosUnitCancellation` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientModels` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientMultiplication` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.PointConeLiftsChainNaturality` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.StrictQuotientCompletionRealization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.StrictQuotientConeAugmentation` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |

## Status

landed 20261026T092852-L-3475163 2026-10-26 (merge of deliver/V2/Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent)
