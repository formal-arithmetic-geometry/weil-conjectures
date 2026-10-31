/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow

/-! Evaluation in the braided right tensor presentation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe a b c d
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

private theorem rightCounit {C : Type a} [Category.{b} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] (K M : C) :
    (finiteHomClosed (C := C)).evaluation K M =
      (β_ K ((ihom K).obj M)).inv ≫ (ihom.ev K).app M := by
  change (tensorRight K).map (𝟙 ((ihom K).obj M)) ≫
    ((β_ K ((ihom K).obj M)).inv ≫ (ihom.ev K).app M) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Evaluation of the left tensor adjunct in the right tensor closed presentation.
Source: blueprint thm-coef-finite-hom, opening evaluation paragraph.
(blueprint: lem-coef-finite-hom-braided-evaluation).

Proof: the right tensor counit is the left tensor counit preceded by the inverse
braiding. Naturality moves the adjunct across this braiding. The adjunction's
homEquiv_counit identity cancels the adjunct. The assumed scalar braid square
then identifies the result with scalar extension of right evaluation. -/
theorem finiteHom_braided_evaluation
    {C : Type a} [Category.{b} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] {D : Type c} [Category.{d} D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] (F : C ⥤ D) (K M : C)
    (t : ∀ P Q : C, F.obj P ⊗ F.obj Q ⟶ F.obj (P ⊗ Q))
    (ht : (β_ (F.obj K) (F.obj ((ihom K).obj M))).inv ≫
        t K ((ihom K).obj M) = t ((ihom K).obj M) K ≫
          F.map (β_ K ((ihom K).obj M)).inv) :
    (finiteHomClosed (C := D)).tensor.map
        (Prod.mkHom (((ihom.adjunction (F.obj K)).homEquiv _ _)
          (t K ((ihom K).obj M) ≫ F.map ((ihom.ev K).app M))) (𝟙 (F.obj K))) ≫
        (finiteHomClosed (C := D)).evaluation (F.obj K) (F.obj M) =
      t ((ihom K).obj M) K ≫ F.map ((finiteHomClosed (C := C)).evaluation K M) := by
  rw [rightCounit, rightCounit]
  simp only [CoefficientClosedStructure.tensor, finiteHomClosed, tensor_map, tensorHom_id,
    CategoryTheory.Functor.id_obj]
  rw [← Category.assoc, BraidedCategory.braiding_inv_naturality_left, Category.assoc]
  have he := (ihom.adjunction (F.obj K)).homEquiv_counit _ (F.obj M)
    (((ihom.adjunction (F.obj K)).homEquiv _ _)
      (t K ((ihom K).obj M) ≫ F.map ((ihom.ev K).app M)))
  rw [Equiv.symm_apply_apply] at he
  change t K ((ihom K).obj M) ≫ F.map ((ihom.ev K).app M) =
    F.obj K ◁ _ ≫ (ihom.ev (F.obj K)).app (F.obj M) at he
  rw [← he, ← Category.assoc, ht, Category.assoc, ← F.map_comp]

end WeilConjectures
