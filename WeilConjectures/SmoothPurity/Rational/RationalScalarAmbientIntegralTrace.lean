/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction

/-! # Integral ambient trace before rational localization

This is the integral derived part of the ambient trace argument. It is kept
separate from the denominator-clearing transport through scalar localization.
(blueprint: new-sf-rational-scalar-ambient-integral-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- Integral trace data, before passing to the scalar-localized categories.
Source: Bhatt--Scholze, Proposition 6.8.14(2), finite separable trace and
finite-free completed scalar comparison.
(blueprint: new-sf-rational-scalar-ambient-integral-trace).

Proof: choose a trace-dual basis for the finite separable extension F/E. The
usual restriction/coextension unit and counit are finite sums, so one common
integral denominator makes them maps of completed coefficient sheaves. The
trace-dual identities prove the two triangles on complexes and on roofs in the
derived category. Exactness of restriction and finite-free extension carries
the construction through the chosen derived restriction; the comparison for a
complete E-object identifies the finite-free extension with the recorded
integral scalar extension. The same formulas commute with every constructible
map, giving the displayed naturality equation. -/
theorem rationalScalarAmbientIntegralTrace
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W)) :
    ∃ e : ∀ M : sfIntegralConstructibleCategory l E W,
      ((rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj) ≃
        (K ⟶ ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj M).obj),
      ∀ (M N : sfIntegralConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ f.hom) =
          e M h ≫ ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).map f).hom := by
  sorry

end WeilConjectures
