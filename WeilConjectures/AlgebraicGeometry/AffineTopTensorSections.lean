/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Whole-scheme affine tensor sections

Source: Stacks Project, Tags 01I9 and 01IA. -/

@[expose] public section
universe u
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
-- Compare the affine-open algebra instance with the whole-scheme algebra instance.
/-- The affine sections comparison specialized to the whole source and target schemes
(Stacks, Tags 01I9 and 01IA). -/
theorem exists_affineTopTensorSections {A B : Scheme.{u}} (f : B ⟶ A)
    (G : A.Modules) (hG : G.IsQuasicoherent) (hA : IsAffine A) (hB : IsAffine B) :
    letI : Algebra Γ(A, ⊤) Γ(B, ⊤) := f.appTop.hom.toAlgebra
    ∃ d : (Γ(G, ⊤) ⊗[Γ(A, ⊤)] Γ(B, ⊤)) →+
      Γ((Modules.tensorPullback f).obj G, ⊤),
      Function.Bijective d ∧ ∀ (m : Γ(G, ⊤)) (b : Γ(B, ⊤)),
        d (m ⊗ₜ[Γ(A, ⊤)] b) = b • Modules.tensorSectionsUnit f G m := by
  classical
  let : IsAffine A := hA
  let : IsAffine B := hB
  let A' : A.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let B' : B.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hle : B'.1 ≤ f ⁻¹ᵁ A'.1 := by simp [A', B']
  have happ : f.appLE A'.1 B'.1 hle = f.appTop := by
    have hi : (homOfLE hle).op = 𝟙 (op (⊤ : B.Opens)) := rfl
    unfold Scheme.Hom.appLE
    erw [hi, B.presheaf.map_id, Category.comp_id]
  have H := Modules.exists_tensorPullback_affine_sections f A' B' hle
  dsimp only at H
  obtain ⟨c, hc, _, hp, _⟩ := H
  have H' :
      letI : Algebra Γ(A, A'.1) Γ(B, B'.1) := (f.appLE A'.1 B'.1 hle).hom.toAlgebra
      ∃ d : (Γ(G, A'.1) ⊗[Γ(A, A'.1)] Γ(B, B'.1)) →+
        Γ((Modules.tensorPullback f).obj G, B'.1),
        Function.Bijective d ∧ ∀ (m : Γ(G, A'.1)) (b : Γ(B, B'.1)),
          d (m ⊗ₜ[Γ(A, A'.1)] b) = b • Modules.tensorSectionsUnit f G m :=
    ⟨(c G hG).toAddMonoidHom, hc G hG, hp G hG⟩
  rw [happ] at H'
  exact H'


end AlgebraicGeometry.Scheme
