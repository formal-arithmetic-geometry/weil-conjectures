/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # The tensor-unit law for the closed-transpose action -/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace CategoryTheory
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)
/-- The tensor-Hom action at the tensor unit is the internal-Hom right unitor.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-unit).
Proof: untranspose the equality. Adjunction naturality makes the left side the
uncurried action followed by the right unitor. The unit formula for braiding
removes the exchange, and monoidal coherence identifies the result with the
right unitor tensored with K, followed by evaluation. This is the untranspose
of the required right unitor. -/
theorem tensorHomAction_unit (β : @SymmetricCategory D _ S.monoidal) (K L : D) :
    tensorHomAction S β K L S.monoidal.tensorUnit ≫
      H.map (Prod.mkHom (𝟙 (op K)) (S.monoidal.rightUnitor L).hom) =
        (S.monoidal.rightUnitor (H.obj (op K, L))).hom := by
  let _ := S.monoidal
  let _ := β
  apply (S.transpose _ K L).symm.injective
  unfold tensorHomAction CoefficientClosedStructure.transpose
  erw [(S.adjunction K).homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
  change _ = ((ρ_ (H.obj (op K, L))).hom ▷ K) ≫ S.evaluation K L
  dsimp only [CoefficientClosedStructure.tensor]
  simp only [tensor_map, tensorHom_id, id_tensorHom, braiding_tensorUnit_left,
    whiskerLeft_comp, Category.assoc]
  monoidal

end CategoryTheory
