/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Compatibilities of projection maps

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, let `T_C`, `T_D` be bifunctors (tensor
products, written `⊗`) and `φ : F (a ⊗ b) ⟶ F a ⊗ F b` a comparison. The right adjoint
projection map `π : G M ⊗ L ⟶ G (M ⊗ F L)`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) satisfies the following
compatibilities.

* `CategoryTheory.Adjunction.unit_app_comp_map_rightAdjointProjectionMap`: the unit
  `η : N ⟶ G F N` is compatible with `π` and `φ`.
* `CategoryTheory.Adjunction.rightAdjointProjectionMap_mate`: `π` is compatible with the mate
  `G₁ ⋙ U ⟶ V ⋙ G₂` of a natural transformation `σ : U ⋙ F₂ ⟶ F₁ ⋙ V` compatible with the
  comparisons. This is the compatibility of the projection map with base change.
* `CategoryTheory.Adjunction.rightAdjointProjectionMap_comp`: the projection map of a
  composite of adjunctions is the composite of the projection maps.

Dually, for the projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` of a left adjoint
(`CategoryTheory.Adjunction.projectionMap`):

* `CategoryTheory.Adjunction.projectionMap_mate`: it is compatible with the mate
  `U ⋙ F₂ ⟶ F₁ ⋙ V` of an isomorphism `G₁ ⋙ U ≅ V ⋙ G₂` compatible with the comparisons.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

section RightAdjoint

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The unit `η : N ⟶ G F N` and the right adjoint projection map: the composite
`N ⊗ L ⟶ G F (N ⊗ L) ⟶ G (F N ⊗ F L)` of `η` and `G φ` is `η ⊗ 1` followed by the projection
map `G F N ⊗ L ⟶ G (F N ⊗ F L)`. -/
@[reassoc]
lemma unit_app_comp_map_rightAdjointProjectionMap (N L : D) :
    adj.unit.app ((T_D.obj N).obj L) ≫ G.map ((φ.app N).app L) =
      (T_D.map (adj.unit.app N)).app L ≫
        ((adj.rightAdjointProjectionMap φ).app (F.obj N)).app L := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, adj.counit_naturality]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  have h₂ := NatTrans.congr_app (φ.naturality (adj.unit.app N)) L
  dsimp at h₂ ⊢
  rw [left_triangle_components_assoc, reassoc_of% h₂, ← NatTrans.comp_app, ← T_C.map_comp,
    adj.left_triangle_components, T_C.map_id, NatTrans.id_app, Category.comp_id]

variable {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
  {F₁ : D₁ ⥤ C₁} {G₁ : C₁ ⥤ D₁} (adj₁ : F₁ ⊣ G₁) {F₂ : D₂ ⥤ C₂} {G₂ : C₂ ⥤ D₂} (adj₂ : F₂ ⊣ G₂)
  {T₁ : C₁ ⥤ C₁ ⥤ C₁} {S₁ : D₁ ⥤ D₁ ⥤ D₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂} {S₂ : D₂ ⥤ D₂ ⥤ D₂}
  (φ₁ : (postcompose₂.obj F₁).obj S₁ ⟶ (((whiskeringLeft₂ C₁).obj F₁).obj F₁).obj T₁)
  (φ₂ : (postcompose₂.obj F₂).obj S₂ ⟶ (((whiskeringLeft₂ C₂).obj F₂).obj F₂).obj T₂)
  {U : D₁ ⥤ D₂} {V : C₁ ⥤ C₂}
  (ψU : (postcompose₂.obj U).obj S₁ ⟶ (((whiskeringLeft₂ D₂).obj U).obj U).obj S₂)
  (ψV : (postcompose₂.obj V).obj T₁ ⟶ (((whiskeringLeft₂ C₂).obj V).obj V).obj T₂)
  (σ : U ⋙ F₂ ⟶ F₁ ⋙ V) (ex : G₁ ⋙ U ⟶ V ⋙ G₂)

/-- **The right adjoint projection map is compatible with mates.** Let `σ : U F₂ ⟶ F₁ V` be
compatible with the comparisons `φ₁`, `φ₂`, `ψ_U`, `ψ_V` (hypothesis `hσ`), and let
`ex : G₁ ⋙ U ⟶ V ⋙ G₂` be its mate (hypothesis `hex`, the transpose of `ex` along `adj₂`).
Then the square
```
U (G₁ M ⊗ L) --U π₁--> U G₁ (M ⊗ F₁ L) --ex--> G₂ V (M ⊗ F₁ L) --G₂ ψ_V--> G₂ (V M ⊗ V F₁ L)
     |                                                                         ‖
   ψ_U                                                                         ‖
     v                                                                         ‖
U G₁ M ⊗ U L --ex ⊗ 1--> G₂ V M ⊗ U L --π₂--> G₂ (V M ⊗ F₂ U L) --G₂(1 ⊗ σ)--> G₂ (V M ⊗ V F₁ L)
```
commutes. For derived pullbacks and pushforwards this is the compatibility of the projection
map with the base change map `Ex_*`. -/
lemma rightAdjointProjectionMap_mate
    (hσ : ∀ a b, F₂.map ((ψU.app a).app b) ≫ (φ₂.app (U.obj a)).app (U.obj b) ≫
      (T₂.map (σ.app a)).app _ ≫ (T₂.obj _).map (σ.app b) =
        σ.app ((S₁.obj a).obj b) ≫ V.map ((φ₁.app a).app b) ≫ (ψV.app _).app _)
    (hex : ∀ M, F₂.map (ex.app M) ≫ adj₂.counit.app (V.obj M) =
      σ.app (G₁.obj M) ≫ V.map (adj₁.counit.app M))
    (M : C₁) (L : D₁) :
    U.map (((adj₁.rightAdjointProjectionMap φ₁).app M).app L) ≫
        ex.app ((T₁.obj M).obj (F₁.obj L)) ≫ G₂.map ((ψV.app M).app (F₁.obj L)) =
      (ψU.app (G₁.obj M)).app L ≫ (S₂.map (ex.app M)).app (U.obj L) ≫
        ((adj₂.rightAdjointProjectionMap φ₂).app (V.obj M)).app (U.obj L) ≫
        G₂.map ((T₂.obj (V.obj M)).map (σ.app L)) := by
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  dsimp
  -- the right hand side
  erw [adj₂.counit_naturality ((T₂.obj (V.obj M)).map (σ.app L))]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  have h₁ := NatTrans.congr_app (φ₂.naturality (ex.app M)) (U.obj L)
  dsimp at h₁
  rw [reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← T₂.map_comp, hex]
  -- the left hand side
  rw [adj₂.counit_naturality]
  have h₂ := hex ((T₁.obj M).obj (F₁.obj L))
  dsimp at h₂
  rw [reassoc_of% h₂]
  have h₃ := σ.naturality (((adj₁.rightAdjointProjectionMap φ₁).app M).app L)
  dsimp at h₃
  rw [reassoc_of% h₃, ← V.map_comp_assoc]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  have h₄ := NatTrans.congr_app (ψV.naturality (adj₁.counit.app M)) (F₁.obj L)
  dsimp at h₄
  rw [V.map_comp_assoc, h₄]
  have h₅ := hσ (G₁.obj M) L
  simp only [← Category.assoc] at h₅ ⊢
  rw [← h₅]
  simp only [Category.assoc]
  congr 2
  rw [T₂.map_comp, NatTrans.comp_app_assoc]
  congr 1
  exact ((T₂.map (V.map (adj₁.counit.app M))).naturality (σ.app L))

end RightAdjoint

end CategoryTheory.Adjunction
