/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorConstraints
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenSquareExchange

/-! Finite normalization of the unary integral pullback compositor.
Source: Stacks 099N(5), 0D6D and 0941.
(blueprint: lem-pur-integral-pullback-finite-reduction-composition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The unary compositor has the same finite normalization as the coherent counit pullbacks.
Source: Stacks 099N(5), 0D6D and 0941; finite-reduction clause of
lem-pod-integral-pullback-composition and the normalized inverse-image evaluation.
(blueprint: lem-pur-integral-pullback-finite-reduction-composition)

Proof: choose flat-term K-flat representatives P of K and Q of f-star K. Apply the
finite-reduction equation specifying integralPullbackComposition at exponent n+1.
The adjoint of the tower projection identifies each integralPullbackReductionIso
with the evaluation of the pullback realization followed by its reduction/limit
counit. The reductionEvaluation naturality square cancels the source and target
scalar-reduction identifications. Both finite pullback presentations preserve
adjunction-unit sections. Their unique unit-preserving identification transports
the constant-ring compositor to sfIntrinsicDerivedPullbackComp, since both are
mates of the same restriction compositor. Substitute these three identifications
and cancel the middle presentation isomorphisms. The result is precisely the
stated equation on K. This uses only unary pullbacks, no tensor comparisons and
no inference that separate finite evaluations detect a derived system morphism.
The formula works also for n=0, zero K and empty schemes.
-/
theorem integralPullback_finiteReduction_composition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Z n).map
        ((pullbackTensorCalculus l E Z).reduction.map
          ((pullbackTensorIntegralComposition l E f h).hom.app K).hom) ≫
      (coefficientSequenceDerivedEvaluation l E Z n).map
        (pullbackTensorIntegralReductionPullback l E h
          ((constructibleIntegralPullback l E f).obj K)).hom ≫
      (pullbackTensorDerivedEvaluation l E h n).hom.app
        ((pullbackTensorCalculus l E X).reduction.obj
          ((constructibleIntegralPullback l E f).obj K).obj) ≫
      (finiteDerivedPullback l E n h).map
        ((coefficientSequenceDerivedEvaluation l E X n).map
            (pullbackTensorIntegralReductionPullback l E f K).hom ≫
          (pullbackTensorDerivedEvaluation l E f n).hom.app
            ((pullbackTensorCalculus l E Y).reduction.obj K.obj)) =
    ((coefficientSequenceDerivedEvaluation l E Z n).map
        (pullbackTensorIntegralReductionPullback l E (h ≫ f) K).hom ≫
      (pullbackTensorDerivedEvaluation l E (h ≫ f) n).hom.app
        ((pullbackTensorCalculus l E Y).reduction.obj K.obj)) ≫
      (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj
          ((pullbackTensorCalculus l E Y).reduction.obj K.obj)) := by sorry

end WeilConjectures
