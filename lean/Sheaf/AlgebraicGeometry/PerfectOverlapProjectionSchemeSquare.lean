/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube

/-! # The first-open restriction square for an overlap -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Restricting the composite map to the overlap and then to the first open
equals first restricting the composite map and then taking the overlap.

Proof: Compose both sides with the immersion of the first inverse-image open
into the ambient scheme. The two composites are the same restriction of `gk`;
the immersion is a monomorphism, so the original arrows agree. -/
theorem perfectOverlapRestrictionSquareU
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U V : Y.Opens) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let hPU : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPV : Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPW : P ⊓ Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
      fun _ hx ↦ ⟨hPU hx.1, hPV hx.2⟩
    (gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW) ≫
        K.homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) =
      X.homOfLE (inf_le_left : P ⊓ Q ≤ P) ≫
        gk.resLE (f ⁻¹ᵁ U) P hPU := by
  intro P Q hPU hPV hPW
  apply (cancel_mono (f ⁻¹ᵁ U).ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- The corresponding second-open square is obtained by the same ambient
restriction calculation, using the right projection of the overlap. -/
theorem perfectOverlapRestrictionSquareV
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U V : Y.Opens) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let hPU : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPV : Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPW : P ⊓ Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
      fun _ hx ↦ ⟨hPU hx.1, hPV hx.2⟩
    (gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW) ≫
        K.homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V) =
      X.homOfLE (inf_le_right : P ⊓ Q ≤ Q) ≫
        gk.resLE (f ⁻¹ᵁ V) Q hPV := by
  intro P Q hPU hPV hPW
  apply (cancel_mono (f ⁻¹ᵁ V).ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

end AlgebraicGeometry
