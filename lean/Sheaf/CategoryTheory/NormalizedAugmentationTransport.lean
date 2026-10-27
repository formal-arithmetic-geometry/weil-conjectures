/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Transport of augmentations through a normalized comparison

Source: blueprint main-20261015, `fix-lem-exchanges`, Proof Step 5, direct-image ingredient.
(blueprint: lem-sf-cbc-normalized-augmentation-transport)

The categorical extraction uses no limit, abelian, or derived structure.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {D_U : Type u₁} [Category.{v₁} D_U]
  {D_V : Type u₂} [Category.{v₂} D_V]
  {E_U : Type u₃} [Category.{v₃} E_U]
  {E_V : Type u₄} [Category.{v₄} E_V]

/-- The augmentation induced by `i` and the inverse constant-object identification `j`.
Source: blueprint main-20261015, `fix-lem-exchanges`, Proof Step 5, direct-image ingredient.
(blueprint: lem-sf-cbc-normalized-augmentation-transport) -/
def normalizedAugmentationUnit
    {Δ B : D_U ⥤ E_U} (L : E_U ⥤ D_U) (i : Δ ⟶ B) (j : Δ ⋙ L ≅ 𝟭 D_U) :
    𝟭 D_U ⟶ B ⋙ L :=
  j.inv ≫ Functor.whiskerRight i L

/-- The comparison with components `L_V.map (h.app F) ≫ b.inv.app (B_U.obj F)`.
Naturality is supplied by ordinary whiskering and composition of natural transformations.
Source: blueprint main-20261015, `fix-lem-exchanges`, Proof Step 5, direct-image ingredient.
(blueprint: lem-sf-cbc-normalized-augmentation-transport) -/
def normalizedAugmentationComparison
    (B_U : D_U ⥤ E_U) {B_V : D_V ⥤ E_V}
    {L_U : E_U ⥤ D_U} (L_V : E_V ⥤ D_V)
    {P : D_U ⥤ D_V} {Q : E_U ⥤ E_V}
    (b : L_U ⋙ P ≅ Q ⋙ L_V) (h : P ⋙ B_V ⟶ B_U ⋙ Q) :
    P ⋙ B_V ⋙ L_V ⟶ B_U ⋙ L_U ⋙ P :=
  Functor.whiskerRight h L_V ≫ Functor.whiskerLeft B_U b.inv

/-- A normalized comparison transports the two induced augmentations and is natural.
Source: blueprint main-20261015, `fix-lem-exchanges`, Proof Step 5, direct-image ingredient.
(blueprint: lem-sf-cbc-normalized-augmentation-transport)

Proof plan (the six elementary steps of the node, using `def-nagata-category`):
1. Expand eta_V and apply L_V to the augmentation equation, using functoriality.
2. Substitute the constant-object normalization to replace L_V(chi) after j_V inverse
   by P(j_U inverse) followed by b at Delta_U F.
3. Apply naturality of b at i_U,F, reassociate, and use P's composition law. This gives
   eta_V followed by L_V(h_F) = P(eta_U) followed by b at B_U F.
4. Postcompose with b inverse at B_U F and cancel the inverse pair to obtain the rho equation.
5. Conjugate naturality of b at B_U(t) by its inverse components to obtain inverse naturality.
6. Apply L_V to naturality of h, combine with Step 5, and reassociate. This is precisely
   P(C_U(t)) after rho_F = rho_F' after C_V(P(t)). The comparison definition packages
   the same components as a natural transformation using whiskering and composition.
-/
theorem normalized_augmentation_transport
    (Δ_U B_U : D_U ⥤ E_U) (Δ_V B_V : D_V ⥤ E_V)
    (L_U : E_U ⥤ D_U) (L_V : E_V ⥤ D_V)
    (i_U : Δ_U ⟶ B_U) (i_V : Δ_V ⟶ B_V)
    (j_U : Δ_U ⋙ L_U ≅ 𝟭 D_U) (j_V : Δ_V ⋙ L_V ≅ 𝟭 D_V)
    (P : D_U ⥤ D_V) (Q : E_U ⥤ E_V)
    (χ : P ⋙ Δ_V ≅ Δ_U ⋙ Q) (b : L_U ⋙ P ≅ Q ⋙ L_V)
    (h : P ⋙ B_V ⟶ B_U ⋙ Q)
    (augmentation : ∀ F : D_U,
      i_V.app (P.obj F) ≫ h.app F = χ.hom.app F ≫ Q.map (i_U.app F))
    (normalization : ∀ F : D_U,
      P.map (j_U.inv.app F) ≫ b.hom.app (Δ_U.obj F) =
        j_V.inv.app (P.obj F) ≫ L_V.map (χ.hom.app F)) :
    (∀ F : D_U,
      (normalizedAugmentationUnit L_V i_V j_V).app (P.obj F) ≫ L_V.map (h.app F) =
        P.map ((normalizedAugmentationUnit L_U i_U j_U).app F) ≫ b.hom.app (B_U.obj F) ∧
      (normalizedAugmentationUnit L_V i_V j_V).app (P.obj F) ≫
          (normalizedAugmentationComparison B_U L_V b h).app F =
        P.map ((normalizedAugmentationUnit L_U i_U j_U).app F)) ∧
    (∀ (F F' : D_U) (t : F ⟶ F'),
      (normalizedAugmentationComparison B_U L_V b h).app F ≫ P.map ((B_U ⋙ L_U).map t) =
        (B_V ⋙ L_V).map (P.map t) ≫
          (normalizedAugmentationComparison B_U L_V b h).app F') := by
  constructor
  · intro F
    have hb : b.hom.app (Δ_U.obj F) ≫ L_V.map (Q.map (i_U.app F)) =
        P.map (L_U.map (i_U.app F)) ≫ b.hom.app (B_U.obj F) :=
      (b.hom.naturality (i_U.app F)).symm
    have hη : (normalizedAugmentationUnit L_V i_V j_V).app (P.obj F) ≫
        L_V.map (h.app F) =
        P.map ((normalizedAugmentationUnit L_U i_U j_U).app F) ≫
          b.hom.app (B_U.obj F) := by
      change (j_V.inv.app (P.obj F) ≫ L_V.map (i_V.app (P.obj F))) ≫
          L_V.map (h.app F) =
        P.map (j_U.inv.app F ≫ L_U.map (i_U.app F)) ≫ b.hom.app (B_U.obj F)
      calc
        _ = j_V.inv.app (P.obj F) ≫
            L_V.map (i_V.app (P.obj F) ≫ h.app F) := by
          rw [L_V.map_comp, Category.assoc]
        _ = j_V.inv.app (P.obj F) ≫
            L_V.map (χ.hom.app F ≫ Q.map (i_U.app F)) := by rw [augmentation F]
        _ = (j_V.inv.app (P.obj F) ≫ L_V.map (χ.hom.app F)) ≫
            L_V.map (Q.map (i_U.app F)) := by rw [L_V.map_comp, Category.assoc]
        _ = (P.map (j_U.inv.app F) ≫ b.hom.app (Δ_U.obj F)) ≫
            L_V.map (Q.map (i_U.app F)) := by rw [← normalization F]
        _ = (P.map (j_U.inv.app F) ≫ P.map (L_U.map (i_U.app F))) ≫
            b.hom.app (B_U.obj F) := by rw [Category.assoc, hb, Category.assoc]
        _ = _ := by rw [P.map_comp]
    refine ⟨hη, ?_⟩
    change (normalizedAugmentationUnit L_V i_V j_V).app (P.obj F) ≫
        (L_V.map (h.app F) ≫ b.inv.app (B_U.obj F)) = _
    rw [← Category.assoc, hη, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  · intro F F' t
    exact ((normalizedAugmentationComparison B_U L_V b h).naturality t).symm

end CategoryTheory
