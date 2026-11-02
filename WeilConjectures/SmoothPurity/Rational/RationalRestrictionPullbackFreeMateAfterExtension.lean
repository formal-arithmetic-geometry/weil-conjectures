/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionReflectsIsomorphisms

/-! # The legacy finite-free mate after scalar extension

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
trace-dual-basis coordinates after applying the scalar extension functor.

This compatibility statement belongs to the retired rationalization/Karoubi route.
It remains for existing legacy consumers. The current blueprint definition of
derived direct image uses the condensed module-object construction recorded by
`def-weil-derived-direct-image`; this lemma is not an input to that definition.
(blueprint: new-sf-rational-restriction-pullback-free-mate-after-extension).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Applying the canonical E-to-F scalar extension to the finite-free mate at
an extended object gives an isomorphism.

Proof: choose a finite E-basis of F and its trace-dual basis. On K-flat
representatives, finite-free tensor coordinates identify the two composites
with the same finite direct sum after pullback. The normalized completed
comparison and rational localization preserve this coordinate equality, so the
map obtained by applying the X scalar extension to the canonical mate is
invertible. -/
theorem rationalRestrictionPullback_freeMate_after_extension
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfRationalConstructibleCategory l E Y) :
    IsIso ((sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map
      (((mateEquiv
        (rationalScalarExtension_leftAdjunction l E F ι Y)
        (rationalScalarExtension_leftAdjunction l E F ι X)).symm
        (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv)).natTrans.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M))) := by
  sorry

end WeilConjectures
