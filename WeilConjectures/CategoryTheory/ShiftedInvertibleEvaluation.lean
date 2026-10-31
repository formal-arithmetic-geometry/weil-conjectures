/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.Algebra.Group.Int.Defs

/-! # Evaluation-normalized Hom with a shifted invertible factor

Source: current blueprint, sk-thm-sf-identification.proof.md, first paragraph.
(blueprint: lem-sf-shifted-invertible-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.MonoidalClosed

/-- Shifted tensor-Hom cancellation for an invertible second factor.
Source: blueprint identification proof, first paragraph, tensoring the second
variable of internal Hom with an invertible line and a shift
(blueprint: lem-sf-shifted-invertible-evaluation).

Proof: invertible-factor cancellation identifies Hom(K,T) with Hom(K,1) tensor T,
with its evaluation equation. Shift this isomorphism, use the unique
counit-compatible shift comparison for the right adjoint Hom(K,-), and apply
Hom(K,gamma). Naturality of the tensor shift comparison and the shifted counit
identity give precisely the displayed evaluation equation. No dualizability of K
is needed. The construction also applies to zero objects and to the zero category. -/
theorem shiftedInvertibleEvaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    [HasShift C ℤ] (K T W : C) [(tensorLeft K).CommShift ℤ]
    (hT : IsInvertible T) (n : ℤ) (γ : T⟦n⟧ ≅ W) :
    ∃ j : ((ihom K).obj (𝟙_ C) ⊗ T)⟦n⟧ ≅ (ihom K).obj W,
      K ◁ j.hom ≫ (ihom.ev K).app W =
        ((tensorLeft K).commShiftIso n).hom.app _ ≫
          (shiftFunctor C n).map
            ((α_ K _ T).inv ≫ (ihom.ev K).app (𝟙_ C) ▷ T ≫ (λ_ T).hom) ≫ γ.hom := by
  let : (ihom K).CommShift ℤ := (ihom.adjunction K).rightAdjointCommShift ℤ
  have := (ihom.adjunction K).commShift_of_leftAdjoint ℤ
  let e := (ihomIsoIhomUnitTensor (Iso.refl T) hT K).symm
  let j := (shiftFunctor C n).mapIso e ≪≫
    (((ihom K).commShiftIso n).app T).symm ≪≫ (ihom K).mapIso γ
  refine ⟨j, ?_⟩
  have he : K ◁ e.hom ≫ (ihom.ev K).app T =
      (α_ K _ T).inv ≫ (ihom.ev K).app (𝟙_ C) ▷ T ≫ (λ_ T).hom := by
    simpa [e] using
      whiskerLeft_ihomIsoIhomUnitTensor_inv_comp (Iso.refl T) hT K
  dsimp only [j, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [ihom.ev_naturality]
  have hshift := (ihom.adjunction K).shift_counit_app n T
  change (shiftFunctor C n).map ((ihom.ev K).app T) =
    ((tensorLeft K).commShiftIso n).inv.app ((ihom K).obj T) ≫
      K ◁ ((ihom K).commShiftIso n).inv.app T ≫
        (ihom.ev K).app (T⟦n⟧) at hshift
  have hn := ((tensorLeft K).commShiftIso n).inv.naturality e.hom
  change (shiftFunctor C n).map (K ◁ e.hom) ≫
      ((tensorLeft K).commShiftIso n).inv.app ((ihom K).obj T) =
    ((tensorLeft K).commShiftIso n).inv.app ((ihom K).obj (𝟙_ C) ⊗ T) ≫
      K ◁ (shiftFunctor C n).map e.hom at hn
  rw [← cancel_epi (((tensorLeft K).commShiftIso n).inv.app
    ((ihom K).obj (𝟙_ C) ⊗ T))]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hn, ← reassoc_of% hshift]
  rw [← Functor.map_comp_assoc, he]

end CategoryTheory.MonoidalClosed
