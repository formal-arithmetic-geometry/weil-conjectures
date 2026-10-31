/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
/-! # Coefficient naturality of the tensor-Hom action

Source: Stacks 0BYU and closed-monoidal naturality. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace CategoryTheory
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)
/-- Naturality in the coefficient object of the closed-transpose action.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-coefficient-naturality).
Proof: transpose the square. Move the coefficient map through reassociation,
then through braiding and inverse reassociation. Tensor interchange moves it
past evaluation, giving the same uncurried map on both sides. -/
theorem tensorHomAction_coefficient_naturality
    (β : @SymmetricCategory D _ S.monoidal) (K L : D) {A A' : D} (f : A ⟶ A') :
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, L))) f) ≫ tensorHomAction S β K L A' =
      tensorHomAction S β K L A ≫ H.map (Prod.mkHom (𝟙 (op K))
        (S.tensor.map (Prod.mkHom (𝟙 L) f))) := by
  let _ := S.monoidal
  let _ := β
  unfold tensorHomAction CoefficientClosedStructure.transpose
  apply (S.adjunction K).homEquiv_naturality_left_square
  dsimp [CoefficientClosedStructure.tensor]
  simp only [Category.assoc, tensorHom_id, id_tensorHom,
    associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc, whisker_exchange]

end CategoryTheory
