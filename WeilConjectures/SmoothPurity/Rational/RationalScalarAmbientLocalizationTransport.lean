/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory

/-! # Transport of integral ambient trace through rational localization

This module isolates the denominator and normalized scalar-extension transport.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- A family of integral Hom equivalences from the actual derived restriction of `K`
to the completed integral scalar extension, indexed by integral constructible objects.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralFamily
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W)) :=
  ∀ M : sfIntegralConstructibleCategory l E W,
    ((rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj) ≃
      (K ⟶ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj M).obj)

/-- Postcomposition naturality of an integral family of Hom equivalences.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralNaturality
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K) :=
  ∀ (M N : sfIntegralConstructibleCategory l E W) (f : M ⟶ N) (h),
    e₀ N (h ≫ f.hom) =
      e₀ M h ≫ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).map f).hom

/-- Inclusion of rational constructible objects into the ambient scalar localization
(the same expression as `rationalScalarAmbientInclusion` of the item module, which
cannot be imported here).
Source: the raw rationalization Hom formula
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientTransportInclusion :=
  ScalarLocalization.fullSubcategoryInclusion (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)

/-- Rationalized trace transport from the integral trace data.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, and the raw
scalar-localization Hom formula.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).

Proof: tensor the integral equivalences with the localization coefficient ring,
then use the full-subcategory Hom equivalence on both sides. Pure tensors are
independent of their chosen denominators by balancing, and tensor induction
extends the calculation to all localized morphisms. The defining equations of
the normalized rational scalar extension identify the transported map with the
specified functor. Applying the same calculation to postcomposition proves the
displayed naturality equation. -/
theorem rationalScalarAmbientLocalizationTransport
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀) :
    ∃ e : ∀ M : sfRationalConstructibleCategory l E W,
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        (rationalScalarAmbientTransportInclusion l E W).obj M) ≃
      (ScalarLocalization.mk K ⟶
        (rationalScalarAmbientTransportInclusion l F W).obj
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)),
      ∀ (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ (rationalScalarAmbientTransportInclusion l E W).map f) =
          e M h ≫ (rationalScalarAmbientTransportInclusion l F W).map
            ((sfRationalScalarExtension l E W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f) := by
  sorry

end WeilConjectures
