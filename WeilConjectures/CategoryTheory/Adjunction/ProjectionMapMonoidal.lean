/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Associativity and unitality of projection maps

Let `C` and `D` be monoidal categories.

For an adjunction `adj : F ⊣ G` with `F : D ⥤ C` and a comparison
`φ : F (a ⊗ b) ⟶ F a ⊗ F b` satisfying the associativity (resp. right unitality) axiom of an
oplax monoidal functor, the right adjoint projection map `π : G M ⊗ L ⟶ G (M ⊗ F L)`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) is associative (resp. unital):
```
(G M ⊗ L) ⊗ L' --π ▷ L'--> G (M ⊗ F L) ⊗ L' --π--> G ((M ⊗ F L) ⊗ F L')
      | α                                                   | G α
      v                                                     v
G M ⊗ (L ⊗ L') --π--> G (M ⊗ F (L ⊗ L')) --G(M ◁ φ)--> G (M ⊗ (F L ⊗ F L'))
```

Dually, for an adjunction `adj : F ⊣ G` with `F : C ⥤ D`, a functor `G' : D ⥤ C` with a
comparison `μ : G' a ⊗ G' b ⟶ G' (a ⊗ b)` and a comparison `δ : G X ⊗ G' Y ⟶ G (X ⊗ Y)`
compatible with `μ`, the projection map `F (K ⊗ G' M) ⟶ F K ⊗ M`
(`CategoryTheory.Adjunction.projectionMap`) is associative and unital.

## Main statements

- `CategoryTheory.Adjunction.rightAdjointProjectionMap_associativity`,
  `CategoryTheory.Adjunction.rightAdjointProjectionMap_rightUnitality`: associativity and
  unitality of the right adjoint projection map.
- `CategoryTheory.Adjunction.projectionMap_associativity`,
  `CategoryTheory.Adjunction.projectionMap_rightUnitality`: associativity and unitality of the
  projection map of a left adjoint.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory _root_.CategoryTheory.Functor

section RightAdjoint

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- The transpose of the right adjoint projection map, in monoidal notation. -/
@[reassoc]
lemma map_rightAdjointProjectionMap_comp_counit (M : C) (L : D) :
    F.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫ adj.counit.app _ =
      (φ.app (G.obj M)).app L ≫ adj.counit.app M ▷ F.obj L :=
  adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L

/-- The naturality of the comparison `φ` in its first variable, in monoidal notation. -/
@[reassoc]
lemma comparison_naturality_left {X X' : D} (f : X ⟶ X') (Y : D) :
    F.map (f ▷ Y) ≫ (φ.app X').app Y = (φ.app X).app Y ≫ F.map f ▷ F.obj Y :=
  NatTrans.congr_app (φ.naturality f) Y

/-- **Associativity of the right adjoint projection map.** If `φ` satisfies the associativity
axiom of an oplax monoidal functor, then
`(π ▷ L') ≫ π ≫ G α = α ≫ π ≫ G (M ◁ φ)`. -/
@[reassoc]
lemma rightAdjointProjectionMap_associativity
    (hφ : ∀ X Y Z : D, (φ.app (X ⊗ Y)).app Z ≫ (φ.app X).app Y ▷ F.obj Z ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ (φ.app X).app (Y ⊗ Z) ≫ F.obj X ◁ (φ.app Y).app Z)
    (M : C) (L L' : D) :
    ((adj.rightAdjointProjectionMap φ).app M).app L ▷ L' ≫
        ((adj.rightAdjointProjectionMap φ).app (M ⊗ F.obj L)).app L' ≫
        G.map (α_ M (F.obj L) (F.obj L')).hom =
      (α_ (G.obj M) L L').hom ≫ ((adj.rightAdjointProjectionMap φ).app M).app (L ⊗ L') ≫
        G.map (M ◁ (φ.app L).app L') := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, adj.counit_naturality]
  erw [map_rightAdjointProjectionMap_comp_counit_assoc, comparison_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc]
  erw [map_rightAdjointProjectionMap_comp_counit]
  rw [comp_whiskerRight_assoc]
  erw [associator_naturality_left, reassoc_of% (hφ (G.obj M) L L')]
  erw [map_rightAdjointProjectionMap_comp_counit_assoc]
  erw [whisker_exchange]
  rfl

/-- **Unitality of the right adjoint projection map.** If `φ` and `η : F (𝟙_ D) ⟶ 𝟙_ C` satisfy
the right unitality axiom of an oplax monoidal functor, then `π ≫ G (M ◁ η) ≫ G ρ = ρ`. -/
lemma rightAdjointProjectionMap_rightUnitality (η : F.obj (𝟙_ D) ⟶ 𝟙_ C)
    (hη : ∀ X : D, (φ.app X).app (𝟙_ D) ≫ F.obj X ◁ η ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom)
    (M : C) :
    ((adj.rightAdjointProjectionMap φ).app M).app (𝟙_ D) ≫ G.map (M ◁ η) ≫
        G.map (ρ_ M).hom = (ρ_ (G.obj M)).hom := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, adj.counit_naturality]
  erw [adj.counit_naturality_assoc, map_rightAdjointProjectionMap_comp_counit_assoc]
  rw [← whisker_exchange_assoc, rightUnitor_naturality, reassoc_of% (hη (G.obj M))]

end RightAdjoint

section LeftAdjoint

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C)
  (δ : (((whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
    (postcompose₂.obj G).obj (curriedTensor D))

/-- The unit of `adj` followed by `G` of the projection map, in monoidal notation. -/
@[reassoc]
lemma unit_app_comp_map_projectionMap (K : C) (M : D) :
    adj.unit.app _ ≫
        G.map (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M) =
      adj.unit.app K ▷ G'.obj M ≫ (δ.app (F.obj K)).app M :=
  adj.unit_app_comp_map_projectionMap_app_app G' _ _ δ K M

/-- **Associativity of the projection map of a left adjoint.** If `δ` is compatible with a
comparison `μ : G' Y ⊗ G' Z ⟶ G' (Y ⊗ Z)` (hypothesis `hδ`), then
`p ≫ (p ▷ N') ≫ α = F (α ≫ K ◁ μ) ≫ p` for the projection map `p : F (K ⊗ G' N) ⟶ F K ⊗ N`. -/
@[reassoc]
lemma projectionMap_associativity (μ : ∀ Y Z : D, G'.obj Y ⊗ G'.obj Z ⟶ G'.obj (Y ⊗ Z))
    (hδ : ∀ X Y Z : D, (δ.app X).app Y ▷ G'.obj Z ≫ (δ.app (X ⊗ Y)).app Z ≫
      G.map (α_ X Y Z).hom =
        (α_ (G.obj X) (G'.obj Y) (G'.obj Z)).hom ≫ G.obj X ◁ μ Y Z ≫ (δ.app X).app (Y ⊗ Z))
    (K : C) (N N' : D) :
    ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app
        (K ⊗ G'.obj N)).app N' ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app N ▷ N' ≫
        (α_ (F.obj K) N N').hom =
      F.map ((α_ K (G'.obj N) (G'.obj N')).hom ≫ K ◁ μ N N') ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app (N ⊗ N') := by
  apply (adj.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [unit_app_comp_map_projectionMap_assoc, adj.unit_naturality_assoc,
    adj.unit_naturality_assoc, unit_app_comp_map_projectionMap]
  have h₁ := NatTrans.congr_app (δ.naturality
    (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app N)) N'
  dsimp at h₁ ⊢
  erw [← reassoc_of% h₁]
  rw [← comp_whiskerRight_assoc]
  erw [unit_app_comp_map_projectionMap]
  rw [comp_whiskerRight_assoc]
  erw [hδ, associator_naturality_left_assoc, whisker_exchange_assoc]
  rfl

/-- **Unitality of the projection map of a left adjoint.** If `δ` and a comparison
`ε : 𝟙_ C ⟶ G' (𝟙_ D)` satisfy the right unitality axiom (hypothesis `hε`), then
`F (ρ⁻¹ ≫ K ◁ ε) ≫ p = ρ⁻¹` for the projection map `p : F (K ⊗ G' 𝟙) ⟶ F K ⊗ 𝟙`. -/
lemma projectionMap_rightUnitality (ε : 𝟙_ C ⟶ G'.obj (𝟙_ D))
    (hε : ∀ X : D, G.obj X ◁ ε ≫ (δ.app X).app (𝟙_ D) ≫ G.map (ρ_ X).hom = (ρ_ (G.obj X)).hom)
    (K : C) :
    F.map ((ρ_ K).inv ≫ K ◁ ε) ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app (𝟙_ D) =
      (ρ_ (F.obj K)).inv := by
  apply (adj.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [adj.unit_naturality_assoc, adj.unit_naturality_assoc, unit_app_comp_map_projectionMap]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  congr 1
  rw [← cancel_mono (G.map (ρ_ (F.obj K)).hom), Category.assoc, Category.assoc]
  erw [hε (F.obj K)]
  rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
  exact Iso.inv_hom_id (ρ_ (G.obj (F.obj K)))

end LeftAdjoint

end CategoryTheory.Adjunction
