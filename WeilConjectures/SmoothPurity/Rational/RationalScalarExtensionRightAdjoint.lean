/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible

/-! # The left adjoint to finite rational scalar extension

This is the trace-dual-basis step of the finite coefficient argument.

## Implementation details

Restriction along the completed coefficient inclusion is exact and preserves constructibility
and derived completeness, since `𝒪_F` is finite free over `𝒪_E`. For a basis `b_i` of `F/E`
with trace-dual basis `c_i`, the unit `m ↦ ∑ b_i ⊗ c_i m` and counit `z ⊗ m ↦ Tr_{F/E}(z) m`
give, after clearing a common denominator, an adjunction with restriction as left adjoint. It
is conjugated by `finiteFreeCompletedScalarComparison` and the normalized rational scalar
comparison to give a left adjoint to the recorded scalar functor.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2, Proposition 6.8.14(2),
  Remark 6.8.15.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Finite rational scalar extension is also a right adjoint. -/
theorem rationalScalarExtension_isRightAdjoint
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).IsRightAdjoint := by
  classical
  let T := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let IE := rationalScalarAmbientInclusion l E W
  let IF := rationalScalarAmbientInclusion l F W
  let fE := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)
  let fF := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l F)
    (DerivedCategory (scalarReductionSource l F W)) (sfIntegralConstructible l F W)
    (Padic.coefficientExtensionUniformizer l F)
  let Uobj (K : sfRationalConstructibleCategory l F W) :
      sfRationalConstructibleCategory l E W :=
    ⟨⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩⟩
  have traceData := fun K : sfRationalConstructibleCategory l F W ↦
    rationalScalarAmbientTrace l E W F ι K.obj.obj
  let e (K : sfRationalConstructibleCategory l F W)
      (M : sfRationalConstructibleCategory l E W) :
      (Uobj K ⟶ M) ≃ (K ⟶ T.obj M) :=
    (fE.homEquiv).trans
      (((traceData K).choose M).trans fF.homEquiv.symm)
  have he (K : sfRationalConstructibleCategory l F W)
      (M N : sfRationalConstructibleCategory l E W) (g : M ⟶ N) (h : Uobj K ⟶ M) :
      e K N (h ≫ g) = e K M h ≫ T.map g := by
    apply fF.map_injective
    change IF.map (fF.preimage ((traceData K).choose N (IE.map (h ≫ g)))) =
      IF.map (fF.preimage ((traceData K).choose M (IE.map h)) ≫ T.map g)
    rw [fF.map_preimage, IF.map_comp, fF.map_preimage, IE.map_comp]
    exact (traceData K).choose_spec M N g (IE.map h)
  exact (Adjunction.adjunctionOfEquivLeft e he).isRightAdjoint

end WeilConjectures
