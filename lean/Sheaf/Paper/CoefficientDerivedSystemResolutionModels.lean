/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Normalized resolution models for coefficient systems

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YY, 07A4, 07A6,
08J9, 0A95, 0D6E and 0941; the existing sequence-site and semilinear constructions
(blueprint: lem-coef-derived-system-resolution-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Construct the normalized fiber calculus and the simultaneous sections/limit models.
The enriched isomorphism field is supplied by the proved closed-adjunction calculation;
this assertion does not include gamma's projection, naturality, Hom-zero or composition
identities. It also records ordinary sections projections and the finite scalar
H-zero normalization, which are separate from the enriched gamma equations.
Source: Stacks 06YS, 06YY, 07A4, 07A6, 08J9, 0A95, 0D6E, 0941;
node lem-coef-derived-system-evaluation-calculus, construction steps 1--5
(blueprint: lem-coef-derived-system-resolution-models).

Proof:
1. Apply SequenceProjection.derivedAdjunction and pushforwardLimitProjections to
   the completed coefficient sheaf and its actual quotient tower. Transport across
   strictSystemSequenceEquivalence and the exact scalar-restriction comparison.
   Uniqueness of right derived functors identifies their direct image with the
   specified coefficientSequenceLimit. Transport the adjunction across that isomorphism.
   The projection normalizations give unit_projection and counit_projection. The
   left-derived comparison on one flat-term K-flat representative gives reductionModel.
2. Apply ringedDerived_closed_symmetric_monoidal on the integral, sequence and finite
   ringed sites. Use its tensor models and the canonical tensor-pullback theorem for
   reduction, scalar extension and evaluation. On the same representatives their
   squares are the ordinary pure-tensor squares. The already fixed scalar/evaluation
   comparisons and their uniqueness identify them with coefficientScalarTensorIso and
   coefficientEvaluationTensorIso. The strict quotient maps give the reduction square.
   Iterating scalar extension identifies each reduction transition-adjoint with the
   associativity isomorphism, so every reduced object is normalized. Apply the same
   argument to each finite quotient, retaining the ordinary 1 tensor x unit and the
   localization counit, to obtain quotientCalculus with its three normalizations.
3. Apply semilinearDerivedSections to the actual ring sequence. Its finite-prefix
   adjunction identifies Hom on normalized systems with finite internal Hom, with its
   evaluation and naturality equations. Uniqueness of the closed transpose identifies
   its actual transitions with the finite quotient comparison and the normalization
   isomorphisms. The same transpose calculation for the sequence projection gives beta
   and beta_evaluation; ringedPullbackHomEvaluationComparison gives its evaluation,
   transpose and composition equations. Componentwise acyclicity gives joint detection
   of derived isomorphisms.
4. Use coefficientSequenceGlobalSectionsEvaluation and its normalized derived pairs.
   Transport the ordinary sections functors by their identity-on-sections isomorphisms
   to coefficientOrdinarySections. Uniqueness of the universal derived comparisons
   gives scalarSections and systemSectionsEvaluation with their model equations.
   Define globalEvaluation as systemSectionsEvaluation followed by sections of fiberHom.
   This makes globalEvaluation_model its defining composite, without an arbitrary lift.
5. Apply coefficientSequenceSectionsLimitComparison to those same derived pairs.
   Identify its limit functors with the prescribed coefficientConstantTowerLimit and
   coefficientMappingLimit by their universal derived comparison units. The ordinary
   comparison is coefficientSectionsLimitIso because both commute with every ordinary
   projection. Whisker by the exact sequence restriction. The resulting comparison is
   kappa below; the theorem's resolution equation is exactly globalLimit_model after
   these transports. All scalar-section transports retain their ordinary section
   formulas and universal-unit equations. Package these comparisons and equations as D.
   Retain its actual-projection clause as sections_projection for arbitrary M.
   Normalize finite closed transposition by the Hom-complex evaluation on the chosen
   K-flat/K-injective pair. On degree-zero cocycle classes the finite enriched scalar
   comparison is the extension/restriction Hom bijection; the coefficientHomZeroEquiv
   normalizations give scalar_hom_zero. These are the two ProjectionModels equations.
   Insert the already proved coefficientClosedEnriched_isIso as the enriched field.
No projection identity for gamma, composition identity, reconstruction isomorphism, or
invertibility of beta on arbitrary inputs is used in this construction. -/
theorem coefficientDerivedSystemResolutionModels :
    ∃ (F : CoefficientDerivedSystemFibers l E W)
      (κ : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
        coefficientSequenceDerivedRestriction l E W ⋙
          (coefficientTowerSections l E W).rightDerivedFunctor ⋙
            coefficientMappingLimit.{max u (t+1)}),
      let S : CoefficientDerivedSystemCalculus l E W :=
        { toCoefficientDerivedSystemFibers := F
          enriched_isIso := fun P N _ ↦ coefficientClosedEnriched_isIso
            F.integralClosed F.systemClosed F.reduction F.adjunction F.reductionTensor P N
          globalLimit := κ }
      ∃ D : CoefficientDerivedSystemResolutionCoherence l E W S,
        CoefficientDerivedSystemProjectionModels l E W S D := by sorry

end WeilConjectures
