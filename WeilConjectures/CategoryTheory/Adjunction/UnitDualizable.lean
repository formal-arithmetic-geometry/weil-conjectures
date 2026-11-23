/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable

/-!

# The unit of an adjunction at dualizable objects

Let `F ⊣ G` be an adjunction between monoidal categories. The lax tensor map
`G F B ⊗ G A ⟶ G (F B ⊗ A)` of the right adjoint, precomposed with the unit `B ⟶ G F B`, is the
left projection morphism (`CategoryTheory.Adjunction.whiskerRight_unit_comp_homEquiv`).

If `F` is strong monoidal and a strong monoidal functor `I` inverts the unit at `𝟙`, then `I`
inverts the unit at every dualizable object
(`CategoryTheory.Adjunction.isIso_map_unit_app_of_isDualizable`).

## Proof

Up to the tensor structure of `F`, the unit at `W ⊗ 𝟙` is `W ◁ η_𝟙` followed by the left
projection morphism `W ⊗ G F 𝟙 ⟶ G (F W ⊗ F 𝟙)`, which is invertible for dualizable `W`
(`CategoryTheory.Adjunction.isIso_leftProjectionMorphism_of_isDualizable`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

section

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The lax tensor map `G F B ⊗ G A ⟶ G (F B ⊗ A)` of the right adjoint `G` (the transpose of the
tensor product of the counits), precomposed with the unit `B ⟶ G F B`, is the left projection
morphism `B ⊗ G A ⟶ G (F B ⊗ A)`. -/
lemma whiskerRight_unit_comp_homEquiv (B : D) (A : C) :
    adj.unit.app B ▷ G.obj A ≫ adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ F (G.obj (F.obj B)) (G.obj A) ≫
          (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)) =
      adj.leftProjectionMorphism B A := by
  rw [← homEquiv_naturality_left, leftProjectionMorphism]
  congr 1
  refine (Functor.OplaxMonoidal.δ_natural_left_assoc F (adj.unit.app B) (G.obj A)
    (adj.counit.app (F.obj B) ⊗ₘ adj.counit.app A)).symm.trans ?_
  congr 1
  rw [← tensorHom_id, tensorHom_comp_tensorHom]
  erw [left_triangle_components]
  rw [Category.id_comp, id_tensorHom]
  rfl

end

variable {C D E : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  [Category E] [MonoidalCategory E] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
  (I : D ⥤ E) [I.Monoidal]

/-- For an adjunction `F ⊣ G` with `F` strong monoidal and a strong monoidal functor `I`, if `I`
inverts the unit of the adjunction at `𝟙`, it inverts the unit at every dualizable object. -/
lemma isIso_map_unit_app_of_isDualizable {W : D} (hW : IsDualizable W)
    [IsIso (I.map (adj.unit.app (𝟙_ D)))] : IsIso (I.map (adj.unit.app W)) := by
  let := adj.rightAdjointLaxMonoidal
  have := adj.isIso_leftProjectionMorphism_of_isDualizable hW (F.obj (𝟙_ D))
  have : IsIso (I.map (W ◁ adj.unit.app (𝟙_ D))) := by
    rw [Functor.Monoidal.map_whiskerLeft]
    infer_instance
  have key : adj.unit.app (W ⊗ 𝟙_ D) ≫ G.map (Functor.OplaxMonoidal.δ F W (𝟙_ D)) =
      W ◁ adj.unit.app (𝟙_ D) ≫ adj.leftProjectionMorphism W (F.obj (𝟙_ D)) := by
    rw [adj.unit_app_tensor_comp_map_δ, ← adj.whiskerRight_unit_comp_homEquiv, tensorHom_def',
      Category.assoc]
    rfl
  have : IsIso (I.map (adj.unit.app (W ⊗ 𝟙_ D))) := by
    have h : IsIso (I.map (W ◁ adj.unit.app (𝟙_ D) ≫
        adj.leftProjectionMorphism W (F.obj (𝟙_ D)))) := by
      rw [I.map_comp]
      infer_instance
    rw [← key, I.map_comp] at h
    exact IsIso.of_isIso_comp_right _ (I.map (G.map (Functor.OplaxMonoidal.δ F W (𝟙_ D))))
  have h : I.map (adj.unit.app W) = I.map (ρ_ W).inv ≫ I.map (adj.unit.app (W ⊗ 𝟙_ D)) ≫
      I.map (G.map (F.map (ρ_ W).hom)) := by
    rw [← I.map_comp, ← I.map_comp]
    congr 1
    have := adj.unit.naturality (ρ_ W).hom
    simp only [Functor.id_map, Functor.comp_map] at this
    rw [← this, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end CategoryTheory.Adjunction
