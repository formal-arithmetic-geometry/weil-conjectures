/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.FourierTransform.DualBundlePairing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.FourierTransform.CondensedCompactSupportBaseChange
public import WeilConjectures.FourierTransform.Properties.Stalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.Compactification.Over

/-! # Stalks of the condensed Fourier--Deligne transform

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-thm-inversion/lem-fd-stalk-formula.md,
node lem-fd-stalk-formula (blueprint: lem-fd-stalk-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The geometric stalk of the ordinary condensed Fourier--Deligne transform is the
compactly supported derived integral over the geometric fibre, with the pulled-back
Fourier kernel and the relative-dimension shift.  The displayed lower shriek is the
compact-support cohomology of the fibre `V ×_S Spec Ω`, computed using the base change
of the chosen compactification.

Proof (blueprint, lem-fd-stalk-formula.proof.md):
1. Put `W = V ×_S Vdual` and `A = Lp₁^*K ⊗ᴸ K_ψ`. The kernel is locally `Λ_W` in degree
   zero (prop-kernel-lisse), so `A` is bounded constructible (sk-thm-sf-ctf-stability),
   and the transform is bounded constructible (thm-fd-transform-well-defined). Form the
   cartesian square of `ξ` and `p₂`, with `g' : V ×_S Spec Ω ⟶ W` and the base-changed
   compactification of `p₂`. Since `W`, the compactification and `Vdual` are Noetherian
   and the open immersion is quasi-compact, the arbitrary-base compact-support base change
   (det-prop-sf-cbc (b), the form of det-thm-sfb-shriek-base-change for an arbitrary
   `Spec Ω`) gives `Lξ^* Rp₂,! A ≅ Rp'₂,! Lg'^* A`.
2. Derived pullback is monoidal (lem-sfb-derived-pullback-tensor-comparison-iso) and
   composes (prop-sfb-module-left-derived-upper-star-comp), so `Lg'^*Lp₁^*K` is the
   restriction of `K` to the fibre and `Lg'^*K_ψ = L(b ∘ g')^*L_ψ` is the Artin--Schreier
   sheaf of the pairing `⟨x, ξ⟩` (def-fd-kernel). Derived pullback commutes with the
   shift `[r]` of def-fd-transform, giving the displayed isomorphism of derived objects.
Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-thm-inversion/lem-fd-stalk-formula.md, proof paragraphs 1--2
(blueprint: lem-fd-stalk-formula). -/
theorem nonempty_iso_condensedFourierTransform_geometricStalk
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)))
    {S V Vdual : Scheme.{u}} (s : S ⟶ Spec (.of k₀))
    [LocallyOfFiniteType s] [QuasiCompact s] [IsSeparated s]
    {π : V ⟶ S} {πdual : Vdual ⟶ S} (r : ℕ)
    (b : Γ(pullback π πdual, ⊤))
    (bundle : DualBundlePairing π πdual r b)
    [(pullback π πdual).Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd π πdual))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V)))
    (hK : boundedConstructible (condensedRingObj Λ V) K)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ Vdual) :
    Nonempty (
      (moduleObjectDerivedPullback Λ ξ).obj
        ((condensedFourierTransform Λ k₀ π πdual ψ b c (r : ℤ)).obj K) ≅
      (shiftFunctor _ (r : ℤ)).obj
        ((rightDerivedLowerShriekOfCompactification Λ (c.baseChange ξ)).obj
          (((moduleObjectDerivedPullback Λ
              (pullback.fst (pullback.snd π πdual) ξ ≫
                pullback.fst π πdual)).obj K) ⊗
            (moduleObjectDerivedPullback Λ
              (pullback.fst (pullback.snd π πdual) ξ)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (condensedFourierKernel Λ k₀ π πdual ψ b))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
