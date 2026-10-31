/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
/-! # Hom-variable naturality of the tensor-Hom action

Source: Stacks 0BYU and closed-monoidal naturality. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace CategoryTheory
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)
private theorem actionTranspose_left {T T' P Q : D} (f : T' ⟶ T)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ g) =
      f ≫ S.transpose T P Q g := by
  let _ := S.monoidal
  dsimp only [WeilConjectures.CoefficientClosedStructure.transpose,
    WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  rw [tensorHom_id]
  exact (S.adjunction P).homEquiv_naturality_left f g

private theorem actionTranspose_source (T : D) {P P' Q : D} (f : P' ⟶ P)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P' Q (S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q)) := by
  let _ := S.monoidal
  apply (S.transpose T P' Q).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight P').map
    (S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q))) ≫ S.evaluation P' Q
  rw [Functor.map_comp, Category.assoc]
  change _ = (S.transpose T P Q g ▷ P') ≫
    (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q
  rw [show (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q =
    (H.obj (op P, Q) ◁ f) ≫ S.evaluation P Q from S.evaluation_naturality P P' Q f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (T ◁ f) ≫ (S.transpose T P Q).symm (S.transpose T P Q g)
  rw [Equiv.symm_apply_apply]
  simp only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom]

private theorem source_naturality
    (β : @SymmetricCategory D _ S.monoidal) (K K' L A : D) (k : K' ⟶ K) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op (𝟙 L))) (𝟙 A)) ≫
        tensorHomAction S β K' L A = tensorHomAction S β K L A ≫
          H.map (Prod.mkHom k.op (𝟙 (S.tensor.obj (L, A)))) := by
  let _ := S.monoidal
  let _ := β
  unfold tensorHomAction
  rw [← actionTranspose_left, ← actionTranspose_source]
  congr 1
  dsimp [CoefficientClosedStructure.tensor]
  simp only [tensorHom_id, id_tensorHom,
    associator_naturality_left_assoc, associator_naturality_right_assoc]
  have hev : (H.map (Prod.mkHom k.op (𝟙 L)) ▷ K') ≫ S.evaluation K' L =
      (H.obj (op K, L) ◁ k) ≫ S.evaluation K L := S.evaluation_naturality K K' L k
  erw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, hev, comp_whiskerRight]
  rw [← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right,
    whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]
private theorem target_naturality
    (β : @SymmetricCategory D _ S.monoidal) (K L L' A : D) (l : L ⟶ L') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) l)) (𝟙 A)) ≫
        tensorHomAction S β K L' A = tensorHomAction S β K L A ≫
          H.map (Prod.mkHom (𝟙 (op K)) (S.tensor.map (Prod.mkHom l (𝟙 A)))) := by
  let _ := S.monoidal
  let _ := β
  have hev : (H.map (Prod.mkHom (𝟙 (op K)) l) ▷ K) ≫ S.evaluation K L' =
      S.evaluation K L ≫ l := by
    simpa only [CoefficientClosedStructure.evaluation, Functor.comp_map, Prod.sectR,
      tensorRight, curriedTensor, Functor.flip, Functor.id_map] using
      (S.adjunction K).counit.naturality l
  unfold tensorHomAction CoefficientClosedStructure.transpose
  apply (S.adjunction K).homEquiv_naturality_left_square
  dsimp [CoefficientClosedStructure.tensor]
  simp only [Category.assoc, tensorHom_id, id_tensorHom,
    associator_naturality_left_assoc]
  erw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, hev, comp_whiskerRight]

/-- Naturality of the action in both internal-Hom variables at a fixed coefficient.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-hom-naturality).
Proof: for the target variable, transpose the square, move its Hom map through
associators and the exchange, and use naturality of the adjunction counit. For
the source variable, use evaluation dinaturality and braiding naturality after
transposing. Factor a simultaneous Hom map into source and target maps and use
functoriality of tensor and Hom to combine these two squares. -/
theorem tensorHomAction_hom_naturality
    (β : @SymmetricCategory D _ S.monoidal) (K K' L L' A : D)
    (k : K' ⟶ K) (l : L ⟶ L') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op l)) (𝟙 A)) ≫
        tensorHomAction S β K' L' A =
      tensorHomAction S β K L A ≫
        H.map (Prod.mkHom k.op (S.tensor.map (Prod.mkHom l (𝟙 A)))) := by
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op l)) (𝟙 A)) =
      S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op (𝟙 L))) (𝟙 A)) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) l)) (𝟙 A)) := by
    rw [← S.tensor.map_comp]
    congr 1
    ext
    · dsimp
      rw [← H.map_comp]
      congr 1
      ext <;> simp
    · simp
  rw [ht, Category.assoc, target_naturality, ← Category.assoc,
    source_naturality, Category.assoc, ← H.map_comp]
  congr 1
  apply H.congr_map
  ext <;> simp

end CategoryTheory
