/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitZeroCompactSupport
import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitZeroTateSupport
import WeilConjectures.AlgebraicGeometry.RationalAffineLineTrace
import Mathlib.Algebra.CharP.Algebra

/-! The E-coefficient component of the unit Fourier transform zero-fibre calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1600000 in
-- Matching the native derived endpoint types requires extra elaboration heartbeats.
/-- The E-coefficient closed zero-fibre calculation.

Source: latest blueprint, `lem-fd-first-formula.proof.md`, constant-sheaf paragraph.

Proof: first work over the finite ground field. Expand the transform as compact-support
pushforward of the Artin--Schreier kernel, shifted by one. Compact-support base change at
zero identifies its derived restriction with compact-support cohomology of the restricted
kernel. The pairing restricts to zero, and the root-zero trivialization of the character
projector identifies this kernel with the coefficient unit. The rational affine-line trace
identifies its compact-support cohomology with the negative Tate line shifted by minus two.
Adding the Fourier shift gives the negative Tate line shifted by minus one. Push along the
origin and apply the closed-support projection formula to express this as the internal
signed Tate twist of the origin skyscraper. For arbitrary k/k₀, use compact-support and
proper base change, pullback composition and monoidal comparison. Cartesian coefficients,
the kernel pullback comparison and the Tate pullback comparison identify both endpoints
with the displayed objects. Compactification independence allows the given c. The bounded
constructible hypotheses follow from lissity of the character kernel and stability of the
six operations. No trivialization of the Tate line over k is chosen.

(blueprint: lem-fd-unit-closed-fiber-E)
-/
theorem first_formula_unit_closed_fiber_E
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (_hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
 Nonempty ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) := by
  let : CharP k p := charP_of_injective_algebraMap (algebraMap k₀ k).injective p
  obtain ⟨a⟩ := first_formula_unit_zero_compact_support p ℓ hpℓ k₀ E hμ ψ hψ k c
  obtain ⟨trace, _⟩ := RationalAffineLineTrace.exists_compatible_trace ℓ E p hpℓ.symm
  obtain ⟨b⟩ := first_formula_unit_zero_tate_support p ℓ hpℓ E k
  exact ⟨a ≪≫
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.mapIso
        ((shiftFunctor _ (1 : ℤ)).mapIso (trace k)) ≪≫ b⟩

end AlgebraicGeometry.ProEtale
