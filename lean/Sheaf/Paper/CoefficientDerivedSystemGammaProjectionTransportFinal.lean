/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Finite coefficient gamma transport calculation

This is the final finite fiber/base-change calculation used by the transported gamma
projection theorem (blueprint: lem-coef-derived-system-gamma-projection-transport-final).
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

/-- The finite fiber/base-change composition remaining after the section projection
reduction.  It is the concrete specialization of the finite uncurrying and evaluation
identities in the enriched sequence projection formula.
Source: Stacks 07A6, 08JA, 0D6E and 0941.
Proof: apply the finite enriched uncurrying identity, the evaluation-defined fiber
comparison, and functoriality of derived sections and internal Hom; the coefficient
reduction evaluation is natural in the first variable.
(blueprint: lem-coef-derived-system-gamma-projection-transport-final)
-/
theorem coefficientDerivedSystemGammaProjectionTransport_final
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    (coefficientIntegralSections l E W).map
        (@asIso _ _ _ _ (coefficientEnrichedAdjunctionMap S.integralClosed
          S.systemClosed S.reduction S.adjunction S.reductionTensor P N)
          (S.enriched_isIso P N hN)).hom ≫
      (coefficientIntegralSections l E W).map
        ((coefficientSequenceProjection l E W n).app
          ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) ≫
      (D.scalarSections n).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) ≫
      (coefficientFiniteSections l E W n).map
        (S.fiberHom (S.reduction.obj P) N (S.reduction_normalized P) hN n).hom =
    (coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)) ≫
      (coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
          (coefficientFiniteDerivedExtension l E W n)
          (coefficientFiniteAdjunction l E W n) (S.finiteTensor n) P
          ((coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (D.scalarSections n).hom.app
        ((coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientFiniteDerivedExtension l E W n).obj P),
            (coefficientSequenceDerivedEvaluation l E W n).obj N)) ≫
      (coefficientFiniteGlobalHom l E W n).map
        (Prod.mkHom ((S.reductionEvaluation n).hom.app P).op
          (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj N))) := by
  sorry

end WeilConjectures
