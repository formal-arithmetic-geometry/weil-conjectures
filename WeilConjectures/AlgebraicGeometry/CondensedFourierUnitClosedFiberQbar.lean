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

import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitClosedFiberE
import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitClosedFiberScalar

/-! The Qbar-coefficient component of the unit Fourier transform zero-fibre calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1600000 in
-- Matching the native derived endpoint types requires extra elaboration heartbeats.
/-- The Qbar-coefficient closed zero-fibre calculation.

Source: latest blueprint, `lem-fd-first-formula.proof.md`, coefficient and constant-sheaf
paragraphs.

Proof: take the E-coefficient zero-fibre comparison and apply derived coefficient extension
along E → Qbar. Scalar-six exchange commutes with ordinary derived pullback, compact-support
pushforward, closed pushforward, tensor products and shifts. The unit scalar-extends to the
Qbar unit. Finite-etale direct-image exchange and its naturality for translations identify
the scalar extension of the E Artin--Schreier character projector with the projector for the
induced Qbar character. Compatibility of the signed Tate construction identifies the
extended E Tate line with the actual Qbar Tate line. Lissity of the kernel, constructible
stability and finite Tor amplitude supply the exchange hypotheses. Compose the exchanged
E comparison with these endpoint identifications. It has exactly the displayed source and
target, hence gives the required nonempty isomorphism.

(blueprint: lem-fd-unit-closed-fiber-qbar)
-/
theorem first_formula_unit_closed_fiber_Qbar
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
 Nonempty ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ)
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))
        (-1))) := by
  obtain ⟨e⟩ := first_formula_unit_closed_fiber_E p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := first_formula_unit_closed_fiber_scalar p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  exact ⟨a.symm ≪≫
    (WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarClosureDerived
      (AffineSpace PUnit (Spec (.of k))) ℓ E).mapIso e ≪≫ b⟩

end AlgebraicGeometry.ProEtale
