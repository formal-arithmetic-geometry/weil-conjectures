/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.AlgebraicGeometry.RationalAffineLineTrace

/-! Zero restriction before applying the affine-line trace. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Compact-support base change at zero and root-zero evaluation of the AS kernel.

Source: latest blueprint, lem-fd-first-formula.proof.md, constant-sheaf paragraph.

Proof in words. Expand the Fourier transform of the regular unit. The derived pullback
of the unit is the unit, and its tensor product with the AS kernel is the kernel.
Apply compact-support base change along the zero section. The resulting Cartesian
fibre is the affine line, and the pairing is identically zero on it. Root-zero AS
trivialization, compatible with pullback of the character projector, identifies the
restricted kernel with the regular coefficient unit. Commute pullback with the Fourier
shift [1], compare the induced compactification with the standard projective-line chart,
and apply the closed derived pushforward. This gives the displayed compact-support
object, without computing its cohomology or introducing any Tate twist. Equivalently,
one may construct the comparison over k₀ and use compact-support base change for the
arbitrary map Spec k → Spec k₀; no finite-type assumption on this map is used.

(blueprint: lem-fd-unit-zero-compact-support)
-/
theorem first_formula_unit_zero_compact_support
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k]
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
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor).obj
    ((shiftFunctor _ (1 : ℤ)).obj
      (RationalAffineLineTrace.compactSupport ℓ E (Spec (.of k))))) := by
  sorry

end AlgebraicGeometry.ProEtale
