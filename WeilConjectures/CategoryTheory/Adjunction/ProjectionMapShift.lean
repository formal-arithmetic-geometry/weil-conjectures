/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Projection maps commuting with shifts

Let `adj` be an adjunction commuting with shifts (`CategoryTheory.Adjunction.CommShift`), and let
the bifunctors (written `⊗`) commute with shifts in the second variable. If the comparison map of
the projection map commutes with the shifts in the second variable, so does the projection map:

* `CategoryTheory.Adjunction.commShift_rightAdjointProjectionMap_app`: the right adjoint
  projection map `G M ⊗ L ⟶ G (M ⊗ F L)`, as a natural transformation in `L`;
* `CategoryTheory.Adjunction.commShift_projectionMap_app`: the projection map
  `F (K ⊗ G' M) ⟶ F K ⊗ M` of a left adjoint, as a natural transformation in `M`.

Both projection maps are composites of whiskerings of the unit, the counit, the comparison map
and the image of a morphism under the bifunctor, each of which commutes with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {A : Type*} [AddMonoid A] [HasShift C A]
  [HasShift D A]

section RightAdjoint

variable {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)
  [F.CommShift A] [G.CommShift A] [adj.CommShift A]

/-- The right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` commutes with the shifts in `L`
if the comparison `F (G M ⊗ L) ⟶ F G M ⊗ F L` does. -/
lemma commShift_rightAdjointProjectionMap_app (M : C) [(T_D.obj (G.obj M)).CommShift A]
    [(T_C.obj M).CommShift A] [(T_C.obj (F.obj (G.obj M))).CommShift A]
    [NatTrans.CommShift (F₁ := T_D.obj (G.obj M) ⋙ F) (F₂ := F ⋙ T_C.obj (F.obj (G.obj M)))
      (φ.app (G.obj M)) A]
    [NatTrans.CommShift (F₁ := T_C.obj (F.obj (G.obj M))) (F₂ := T_C.obj M)
      (T_C.map (adj.counit.app M)) A] :
    NatTrans.CommShift (F₁ := T_D.obj (G.obj M)) (F₂ := (F ⋙ T_C.obj M) ⋙ G)
      ((adj.rightAdjointProjectionMap φ).app M) A := by
  have e : (adj.rightAdjointProjectionMap φ).app M =
      (T_D.obj (G.obj M)).rightUnitor.inv ≫ whiskerLeft _ adj.unit ≫
        (associator _ _ _).inv ≫
        whiskerRight (G := T_D.obj (G.obj M) ⋙ F) (H := F ⋙ T_C.obj (F.obj (G.obj M)))
          (φ.app (G.obj M)) G ≫
        whiskerRight (whiskerLeft (G := T_C.obj (F.obj (G.obj M))) (H := T_C.obj M) F
          (T_C.map (adj.counit.app M))) G := by
    ext L
    simp [rightAdjointProjectionMap_app_app, homEquiv_unit]
  rw [e]
  infer_instance

end RightAdjoint

section LeftAdjoint

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (δ : (((whiskeringLeft₂ C).obj G).obj G').obj T ⟶ (postcompose₂.obj G).obj T')
  [F.CommShift A] [G.CommShift A] [adj.CommShift A] [G'.CommShift A]

/-- The projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` of a left adjoint commutes with the shifts in
`M` if the comparison `K ⊗ G' M ⟶ G (F K ⊗ M)` does, at `K = G F K`. -/
lemma commShift_projectionMap_app (K : C) [(T.obj K).CommShift A]
    [(T.obj (G.obj (F.obj K))).CommShift A] [(T'.obj (F.obj K)).CommShift A]
    [NatTrans.CommShift (F₁ := T.obj K) (F₂ := T.obj (G.obj (F.obj K)))
      (T.map (adj.unit.app K)) A]
    [NatTrans.CommShift (F₁ := G' ⋙ T.obj (G.obj (F.obj K))) (F₂ := T'.obj (F.obj K) ⋙ G)
      (δ.app (F.obj K)) A] :
    NatTrans.CommShift (F₁ := (G' ⋙ T.obj K) ⋙ F) (F₂ := T'.obj (F.obj K))
      ((adj.projectionMap G' T T' δ).app K) A := by
  have e : (adj.projectionMap G' T T' δ).app K =
      whiskerRight (whiskerLeft (G := T.obj K) (H := T.obj (G.obj (F.obj K))) G'
          (T.map (adj.unit.app K))) F ≫
        whiskerRight (G := G' ⋙ T.obj (G.obj (F.obj K))) (H := T'.obj (F.obj K) ⋙ G)
          (δ.app (F.obj K)) F ≫
        (associator _ _ _).hom ≫ whiskerLeft _ adj.counit ≫ (T'.obj (F.obj K)).rightUnitor.hom := by
    ext M
    simp [projectionMap, projectionMapTranspose]
  rw [e]
  infer_instance

end LeftAdjoint

end CategoryTheory.Adjunction
