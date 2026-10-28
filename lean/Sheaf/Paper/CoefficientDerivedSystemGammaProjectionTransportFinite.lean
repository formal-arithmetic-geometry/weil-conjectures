/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! # Finite enriched transport before sections

This is the unsectioned finite fiber/base-change identity used by the final gamma
projection transport calculation
(blueprint: lem-coef-derived-system-gamma-projection-transport-final).
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

/--
The finite enriched uncurrying and evaluation transport, before applying derived
sections.  It is the strict internal-Hom equation whose image under integral sections,
followed by the scalar-section comparison, is the final gamma projection composite.
Source: Stacks 07A6, 08JA, 0D6E and 0941.
Proof: use the enriched uncurrying identity, the fiber evaluation comparison, and
naturality of reduction evaluation in the first variable.
(blueprint: lem-coef-derived-system-gamma-projection-transport-final)
-/
theorem coefficientDerivedSystemGammaProjectionTransport_finite
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (P : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    coefficientEnrichedAdjunctionMap S.integralClosed S.systemClosed S.reduction
        S.adjunction S.reductionTensor P N ≫
      (coefficientSequenceProjection l E W n).app
        ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N)) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        (S.fiberHom (S.reduction.obj P) N (S.reduction_normalized P) hN n).hom =
    (coefficientIntegralInternalHom l E W).map
        (Prod.mkHom (𝟙 (op P)) ((coefficientSequenceProjection l E W n).app N)) ≫
      coefficientEnrichedAdjunctionMap S.integralClosed (S.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n)
        (coefficientFiniteAdjunction l E W n) (S.finiteTensor n) P
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        ((coefficientFiniteInternalHom l E W n).map
          (Prod.mkHom ((S.reductionEvaluation n).hom.app P).op
            (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj N)))) := by
  sorry

end WeilConjectures
