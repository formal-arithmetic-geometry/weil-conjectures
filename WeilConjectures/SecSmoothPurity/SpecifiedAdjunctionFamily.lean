/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport

/-! # Coefficientwise specified native adjunction families

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/_section.md
(blueprint: def-pur-native-specified-adjunction-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Coefficientwise specified adjunctions used by native smooth purity.
Each field is actual adjunction data on the same restricted compact-support and
twisted-pullback functors. The finite field is the diagonal/DNC normalized
finite-ring adjunction; the integral fields are realized towers; the rational
and closure fields are scalar-localized and finite-subextension adjunctions. -/
structure NativeSpecifiedAdjunctionFamily
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) where
  finite : ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) (s : SmoothDatum D),
    ExplicitAdjunction ell D (.finite A fin n hA) s
  integers : ∀ s : SmoothDatum D,
    ExplicitAdjunction ell D .integers s
  rationals : ∀ s : SmoothDatum D,
    ExplicitAdjunction ell D .rationals s
  integral : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D),
    ExplicitAdjunction ell D (.integral E) s
  rational : ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D),
    ExplicitAdjunction ell D (.rational E) s
  closure : ∀ s : SmoothDatum D,
    ExplicitAdjunction ell D .closure s

/-- The native family selected by the six specified coefficient cases. -/
def NativeSpecifiedAdjunctionFamily.family
    {ell : ℕ} [Fact ell.Prime]
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (N : NativeSpecifiedAdjunctionFamily ell D) : AdjunctionFamily ell D :=
  fun c s => match c with
  | .finite A fin n hA => N.finite A fin n hA s
  | .integers => N.integers s
  | .rationals => N.rationals s
  | .integral E => N.integral E s
  | .rational E => N.rational E s
  | .closure => N.closure s

end AlgebraicGeometry.ProEtale.PurityTransport
