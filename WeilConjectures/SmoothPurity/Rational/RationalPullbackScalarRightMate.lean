/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Rational.RationalScalarExtensionRightAdjoint
import WeilConjectures.SmoothPurity.Rational.RationalRestrictionPullbackUnit

/-! # A single finite coefficient extension and the rational pullback right mate

The finite-free coefficient step of the derived direct-image construction.

## Implementation details

Write `T` for extension of coefficients and `U` for restriction. The finite extension `F/E` is
separable, and the nondegenerate trace pairing makes `U` left adjoint to `T` after inverting
the uniformizer, as well as right adjoint. These adjunctions restrict to the constructible
categories, and `finiteFreeCompletedScalarComparison` identifies the normalized completed scalar
functor with ordinary scalar extension on complete objects.

Transposing the inverse normalized scalar/pullback comparison under `U ⊣ T` gives, on a
flat-term K-flat representative, the comparison between pullback after forgetting the `F`
action and forgetting after pullback, which is invertible. Transposing a second time using the
supplied adjunctions, the iterated mates identity identifies the double transpose with
conjugation between composite adjunctions, which preserves and reflects isomorphisms. No
existence of geometric right adjoints is assumed or concluded.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.7.2 and 6.8.14(2),
  Remark 6.8.15]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The right mate of the normalized pullback comparison for one coefficient inclusion. -/
theorem rationalPullbackScalar_rightMate_isIso
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (RE : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y)
    (RF : sfRationalConstructibleCategory l F X ⥤ sfRationalConstructibleCategory l F Y)
    (aE : rationalDerivedPullback l E f ⊣ RE)
    (aF : rationalDerivedPullback l F f ⊣ RF) :
    IsIso ((mateEquiv aE aF
      (TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv))) := by
  let TX := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let TY := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let : TX.IsRightAdjoint := rationalScalarExtension_isRightAdjoint l E F ι X
  let : TY.IsRightAdjoint := rationalScalarExtension_isRightAdjoint l E F ι Y
  let bX := Adjunction.ofIsRightAdjoint TX
  let bY := Adjunction.ofIsRightAdjoint TY
  obtain ⟨e, he⟩ := rationalRestrictionPullback_unit l E F ι f
    TX.leftAdjoint TY.leftAdjoint bX bY
  let α := TwoSquare.mk _ _ _ _ (rationalPullbackScalarComparison l E F ι f).inv
  let δ := (mateEquiv bY bX).symm α
  have hδ : δ = e.hom := by
    ext K
    apply (bX.homEquiv _ _).injective
    change bX.unit.app _ ≫ TX.map (δ.app K) =
      bX.unit.app _ ≫ TX.map (e.hom.app K)
    rw [← he K]
    exact (unit_mateEquiv_symm bY bX α K).symm
  have : IsIso δ := by
    rw [hδ]
    infer_instance
  have h := iterated_mateEquiv_conjugateEquiv bY bX aF aE δ
  rw [Equiv.apply_symm_apply] at h
  change IsIso (mateEquiv aE aF α)
  rw [h]
  infer_instance

end WeilConjectures
