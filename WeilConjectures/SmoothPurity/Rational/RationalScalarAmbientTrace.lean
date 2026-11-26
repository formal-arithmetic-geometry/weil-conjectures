/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientIntegralTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientLocalizationTransport

/-!
# The ambient rational trace Hom equivalence

This is the trace step of the finite coefficient argument.

## Implementation details

Regard `F` as a finite separable `E`-algebra and choose a basis `b_i` with trace-dual basis
`c_i`. Restriction is left adjoint to ordinary extension, with counit `z ⊗ m ↦ Tr(z) m` and
unit `m ↦ ∑ b_i ⊗ c_i m`. One common integral denominator for all basis, dual basis and trace
coefficients turns these finite formulas into morphisms of the scalar-localized integral
derived categories. For a complete `E`-input, the finite-free completed-scalar comparison is
invertible; composing with it gives the specified rational scalar extension. Only the
`E`-input needs to be complete.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(2), Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- Inclusion of rational constructible objects into the ambient scalar localization. -/
abbrev rationalScalarAmbientInclusion :=
  ScalarLocalization.fullSubcategoryInclusion (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)

/-- The ambient trace equivalence, natural in the complete constructible argument.
The other argument is an arbitrary ambient F-complex, with no constructibility
or completeness hypothesis. Its representing E-object is the actual derived
restriction. -/
theorem rationalScalarAmbientTrace
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W)) :
    ∃ e : ∀ M : sfRationalConstructibleCategory l E W,
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        (rationalScalarAmbientInclusion l E W).obj M) ≃
      (ScalarLocalization.mk K ⟶
        (rationalScalarAmbientInclusion l F W).obj
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)),
      ∀ (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ (rationalScalarAmbientInclusion l E W).map f) =
          e M h ≫ (rationalScalarAmbientInclusion l F W).map
            ((sfRationalScalarExtension l E W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f) := by
  obtain ⟨e₀, he₀⟩ := rationalScalarAmbientIntegralTrace l E W F ι K
  exact rationalScalarAmbientLocalizationTransport l E W F ι K e₀ he₀

end WeilConjectures
