/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The comparison `[A, 𝟙] ⊗ Z ⟶ [A, Z]` along a monoidal functor

For a monoidal functor `G` between monoidal closed categories, the internal hom comparison
`G [A, B] ⟶ [G A, G B]` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) intertwines the
canonical maps `[A, 𝟙] ⊗ Z ⟶ [A, Z]` (`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`) for
`A` and for `G A`: `CategoryTheory.Functor.Monoidal.ihomComparison_ihomUnitTensorToIhom`.
-/

@[expose] public section

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory MonoidalClosed LaxMonoidal OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]

/-- The internal hom comparison of a monoidal functor `G` intertwines the canonical maps
`[A, 𝟙] ⊗ Z ⟶ [A, Z]` for `A` and `G A`:
```
  G [A, 𝟙] ⊗ G Z ──────μ──────▶ G ([A, 𝟙] ⊗ Z) ──G φ──▶ G [A, Z]
        │                                                  │
        ▼                                                  ▼
  [G A, 𝟙] ⊗ G Z ─────────────────φ───────────────▶ [G A, G Z]
```
-/
lemma ihomComparison_ihomUnitTensorToIhom (A Z : C) :
    μ G _ Z ≫ G.map (ihomUnitTensorToIhom A Z) ≫ (ihomComparison G A).natTrans.app Z =
      (((ihomComparison G A).natTrans.app (𝟙_ C) ≫ (ihom (G.obj A)).map (η G)) ▷ G.obj Z) ≫
        ihomUnitTensorToIhom (G.obj A) (G.obj Z) := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq]
  simp only [ihomUnitTensorToIhom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    ihomComparison_ev, whiskerLeft_curry_ihom_ev_app, μ_natural_right_assoc]
  have hl : μ G (𝟙_ C) Z ≫ G.map (λ_ Z).hom = η G ▷ G.obj Z ≫ (λ_ _).hom := by
    rw [LaxMonoidal.left_unitality G, ← comp_whiskerRight_assoc, Monoidal.η_ε, id_whiskerRight,
      Category.id_comp]
  rw [← G.map_comp, whiskerLeft_curry_ihom_ev_app, G.map_comp, G.map_comp,
    LaxMonoidal.associativity_inv_assoc, ← μ_natural_left_assoc]
  erw [hl]
  rw [associator_inv_naturality_middle_assoc, MonoidalCategory.whiskerLeft_comp]
  have hR : (G.obj A ◁ (ihomComparison G A).natTrans.app (𝟙_ C) ≫
      G.obj A ◁ (ihom (G.obj A)).map (η G)) ≫ (ihom.ev (G.obj A)).app (𝟙_ D) =
      (μ G A ((ihom A).obj (𝟙_ C)) ≫ G.map ((ihom.ev A).app (𝟙_ C))) ≫ η G := by
    rw [Category.assoc, ihom.ev_naturality, ihomComparison_ev_assoc, Category.assoc]
  rw [← comp_whiskerRight_assoc _ (η G), ← comp_whiskerRight_assoc _ ((ihom.ev _).app _), hR]
  simp only [comp_whiskerRight, Category.assoc]
  rfl

variable {G} {L : D ⥤ C} (adj : L ⊣ G)

/-- The projection map `L (G A ⊗ T) ⟶ A ⊗ L T` of a left adjoint `L` of a monoidal functor `G`:
the transpose of `G A ⊗ T ⟶ G A ⊗ G L T ⟶ G (A ⊗ L T)`. -/
noncomputable def projectionMap (A : C) : tensorLeft (G.obj A) ⋙ L ⟶ L ⋙ tensorLeft A where
  app T := L.map (G.obj A ◁ adj.unit.app T ≫ μ G A (L.obj T)) ≫ adj.counit.app (A ⊗ L.obj T)
  naturality T T' g := by
    dsimp
    rw [Category.assoc, ← adj.counit_naturality, ← L.map_comp_assoc, ← L.map_comp_assoc]
    congr 2
    rw [Category.assoc, ← μ_natural_right, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, adj.unit_naturality]

/-- The internal hom comparison `G [A, B] ⟶ [G A, G B]` of a monoidal right adjoint `G` is the
conjugate of the projection map `L (G A ⊗ T) ⟶ A ⊗ L T` of its left adjoint. -/
lemma conjugateEquiv_projectionMap (A : C) :
    conjugateEquiv (adj.comp (ihom.adjunction A)) ((ihom.adjunction (G.obj A)).comp adj)
      (projectionMap adj A) = (ihomComparison G A).natTrans := by
  ext B
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, ihomComparison_ev]
  simp only [comp_obj, id_obj, conjugateEquiv_apply_app, curriedTensor_obj_obj,
    Adjunction.comp_unit_app, ihom.ihom_adjunction_unit, comp_map, Adjunction.comp_counit_app,
    curriedTensor_obj_map, ihom.ihom_adjunction_counit, map_comp, Category.assoc,
    MonoidalCategory.whiskerLeft_comp, ihom.ev_naturality, ihom.ev_naturality_assoc,
    ihom.ev_coev_assoc]
  simp only [projectionMap, Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, ← L.map_comp, adj.unit_naturality_assoc]
  rw [adj.right_triangle_components_assoc, Category.assoc, ← μ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, adj.right_triangle_components,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **Internal homs along a monoidal right adjoint.** If the projection map
`L (G A ⊗ T) ⟶ A ⊗ L T` of the left adjoint `L` is an isomorphism, then `G` commutes with
internal homs out of `A`: the comparison `G [A, B] ⟶ [G A, G B]` is an isomorphism. -/
lemma isIso_ihomComparison_of_isIso_projectionMap (A : C) [IsIso (projectionMap adj A)] :
    IsIso (ihomComparison G A).natTrans := by
  rw [← conjugateEquiv_projectionMap adj A]
  infer_instance

/-- If the projection map of the left adjoint of a monoidal functor `G` is an isomorphism at `A`,
and the canonical map `[G A, 𝟙] ⊗ G Z ⟶ [G A, G Z]` is an isomorphism (for instance if `G A` is
dualizable), then `G` sends the canonical map `[A, 𝟙] ⊗ Z ⟶ [A, Z]` to an isomorphism. -/
lemma isIso_map_ihomUnitTensorToIhom (A Z : C) [IsIso (projectionMap adj A)]
    [IsIso (ihomUnitTensorToIhom (G.obj A) (G.obj Z))] :
    IsIso (G.map (ihomUnitTensorToIhom A Z)) := by
  have := isIso_ihomComparison_of_isIso_projectionMap adj A
  have h := ihomComparison_ihomUnitTensorToIhom G A Z
  have h' : IsIso (μ G _ Z ≫ G.map (ihomUnitTensorToIhom A Z) ≫
      (ihomComparison G A).natTrans.app Z) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left (μ G _ Z)
    (G.map (ihomUnitTensorToIhom A Z) ≫ (ihomComparison G A).natTrans.app Z)
  exact IsIso.of_isIso_comp_right _ ((ihomComparison G A).natTrans.app Z)

end CategoryTheory.Functor.Monoidal
