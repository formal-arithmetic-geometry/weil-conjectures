/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import Mathlib.CategoryTheory.Currying

/-! # Projection morphisms as uncurried natural transformations -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The usual proper projection morphism, natural in both variables. -/
def projectionMorphismNatTrans {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal] :
    G.prod (𝟭 D) ⋙ tensor D ⟶ (𝟭 C).prod F ⋙ tensor C ⋙ G where
  app MN := adj.projectionMorphism MN.1 MN.2
  naturality := by
    rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨a, b⟩
    change (G.map a ⊗ₘ b) ≫ adj.projectionMorphism M' N' =
      adj.projectionMorphism M N ≫ G.map (a ⊗ₘ F.map b)
    rw [tensorHom_def, tensorHom_def, G.map_comp, Category.assoc,
      adj.projectionMorphism_natural_right, ← Category.assoc,
      adj.projectionMorphism_natural_left, Category.assoc]

/-- The inverse open projection comparison, natural in both variables. -/
def invProjectionComparisonNatTrans {I : C ⥤ D} {P : D ⥤ C} (adj : I ⊣ P) [P.LaxMonoidal]
    (h : ∀ M N, IsIso (adj.projectionComparison M N)) :
    I.prod (𝟭 D) ⋙ tensor D ⟶ (𝟭 C).prod P ⋙ tensor C ⋙ I := by
  letI := h
  refine { app := fun MN ↦ inv (adj.projectionComparison MN.1 MN.2), naturality := ?_ }
  rintro ⟨M, N⟩ ⟨M', N'⟩ ⟨a, b⟩
  change (I.map a ⊗ₘ b) ≫ inv (adj.projectionComparison M' N') =
    inv (adj.projectionComparison M N) ≫ I.map (a ⊗ₘ P.map b)
  rw [tensorHom_def, tensorHom_def, I.map_comp, Category.assoc,
    adj.inv_projectionComparison_natural_right, ← Category.assoc,
    adj.inv_projectionComparison_natural_left, Category.assoc]

/-- The proper projection map with the tensor functor written in uncurried form. -/
def uncurriedProjectionMorphismNatTrans {F : D ⥤ C} {G : C ⥤ D}
    (adj : F ⊣ G) [F.OplaxMonoidal] :
    G.prod (𝟭 D) ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      (𝟭 C).prod F ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ G where
  app MN := adj.projectionMorphism MN.1 MN.2
  naturality := by
    intro M N φ
    have h := (projectionMorphismNatTrans adj).naturality φ
    simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      curriedTensor_map_app, curriedTensor_obj_map, tensor_map, tensorHom_def] using h

/-- The inverse open projection map with the tensor functor written in uncurried form. -/
def uncurriedInvProjectionComparisonNatTrans {I : C ⥤ D} {P : D ⥤ C}
    (adj : I ⊣ P) [P.LaxMonoidal] (h : ∀ M N, IsIso (adj.projectionComparison M N)) :
    I.prod (𝟭 D) ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      (𝟭 C).prod P ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ I := by
  letI := h
  refine { app := fun MN ↦ inv (adj.projectionComparison MN.1 MN.2), naturality := ?_ }
  intro M N φ
  have hn := (invProjectionComparisonNatTrans adj h).naturality φ
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, tensor_map, tensorHom_def] using hn

end CategoryTheory.Adjunction
