/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.RationalAffineLineTrace

/-! Tate projection formula for the origin. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Closed pushforward of the shifted negative Tate line is the internal twist.

Source: latest blueprint, lem-fd-first-formula.proof.md, trace and support paragraph.

Proof in words. Commute the derived closed pushforward with shifts and compose [-2]
with [1], obtaining [-1]. The cartesian rational Tate comparison identifies the signed
line on Spec k with the pullback of the signed line on the affine line. The closed
support projection formula identifies pushforward of this line with the tensor product
of the pushed unit and the line on the affine line. Transport between the published
native and support-derived operations by their exactness comparisons. This tensor is
precisely spInternalComplexTwist at -1. Thus the displayed object is the required
shifted twist of the origin skyscraper. The assumption p ≠ ℓ supplies invertibility
of ℓ on the characteristic-p field; no trivialization of its Tate Galois action is used.
The assertion contains no Fourier transform, additive character, or trace theorem.

(blueprint: lem-fd-unit-zero-tate-support)
-/
theorem first_formula_unit_zero_tate_support
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [CharP k p] :
  Nonempty (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor).obj
    ((shiftFunctor _ (1 : ℤ)).obj
      (RationalAffineLineTrace.negative ℓ E (Spec (.of k)))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) := by
  sorry

end AlgebraicGeometry.ProEtale
