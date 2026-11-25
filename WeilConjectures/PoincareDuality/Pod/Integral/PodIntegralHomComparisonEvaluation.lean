/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase

/-! # Evaluation square of the integral pullback Hom comparison

We prove the evaluation field of `podIntegralHomComparison_laws`
(`podIntegralHomComparison_evaluation`).

## Implementation details

The proof is formal: the comparison is defined as a transpose, and evaluation is the inverse
transpose of the identity.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The evaluation component of the integral pullback Hom compatibility: the pullback tensor
comparison, followed by the Hom comparison tensored with the identity and evaluation, equals the
pullback of evaluation. -/
theorem podIntegralHomComparison_evaluation :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      (canonicalIntegralPullbackTensor l E g
          ((constructibleIntegralHom l E Y).obj P) P.obj.1.unop).hom ≫
        (constructibleIntegralTensor l E X).map
          (Prod.mkHom (podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P) (𝟙 _)) ≫
        (podIntegralClosed l E X).evaluation
          ((podPairPullback (constructibleIntegralPullback l E g)
            (constructibleIntegralHomPairs l E Y) (constructibleIntegralHomPairs l E X)
            (podIntegralPairs_pullback l E g)).obj P) =
      (constructibleIntegralPullback l E g).map
        ((podIntegralClosed l E Y).evaluation P) := by
  intro P
  have key : ∀ (L : sfIntegralConstructibleCategory l E X)
      (Q : (constructibleIntegralHomPairs l E X).FullSubcategory)
      (f : L ⟶ (constructibleIntegralHom l E X).obj Q),
      (constructibleIntegralTensor l E X).map (Prod.mkHom f (𝟙 _)) ≫
          (podIntegralClosed l E X).evaluation Q =
        ((podIntegralClosed l E X).transpose L Q).symm f := by
    intro L Q f
    apply ((podIntegralClosed l E X).transpose L Q).injective
    rw [(podIntegralClosed l E X).parameter_naturality, PodPartialClosed.evaluation,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Category.comp_id]
  erw [key]
  rw [podPartialHomComparison, AddEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]

end WeilConjectures
