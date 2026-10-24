/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom

/-!
# Composition of left projection morphisms

For projection morphisms `pf_x`, `pf_y`, `pf_{xy}` of composable functors compatible with a
composition isomorphism `L_{xy} ≅ L_x ⋙ L_y` (the associativity pentagon of the projection
formula), the left projection morphisms `M ⊗ L T ⟶ L (F M ⊗ T)` compose in the same way, provided
the braiding of the middle category is symmetric
(`CategoryTheory.Verdier.leftProjection_comp`).
-/

@[expose] public section

namespace CategoryTheory.Verdier

open MonoidalCategory

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃] [MonoidalCategory C₁]
  [MonoidalCategory C₂] [MonoidalCategory C₃] [BraidedCategory C₁] [BraidedCategory C₂]
  [BraidedCategory C₃] {Lx : C₁ ⥤ C₂} {Ly : C₂ ⥤ C₃} {Lxy : C₁ ⥤ C₃} {Fx : C₂ ⥤ C₁}
  {Fy : C₃ ⥤ C₂} {Fxy : C₃ ⥤ C₁}
  (pfx : curriedTensorInsertFunctor₁ Lx ⟶ curriedTensorPost Lx ⋙
    (Functor.whiskeringLeft C₂ C₁ C₂).obj Fx)
  (pfy : curriedTensorInsertFunctor₁ Ly ⟶ curriedTensorPost Ly ⋙
    (Functor.whiskeringLeft C₃ C₂ C₃).obj Fy)
  (pfxy : curriedTensorInsertFunctor₁ Lxy ⟶ curriedTensorPost Lxy ⋙
    (Functor.whiskeringLeft C₃ C₁ C₃).obj Fxy)
  (c : Lxy ≅ Lx ⋙ Ly) (U : Fxy ≅ Fy ⋙ Fx)

/-- **Composition of left projection morphisms**: if the projection morphisms satisfy the
associativity pentagon for `L_{xy} ≅ L_x ⋙ L_y` and `F_{xy} ≅ F_y ⋙ F_x`, and the braiding of the
middle category is symmetric, then
`M ◁ c ≫ LP_y(M, L_x T) ≫ L_y LP_x(F_y M, T) ≫ c⁻¹ = LP_{xy}(M, T) ≫ L_{xy}(U ▷ T)`. -/
lemma leftProjection_comp
    (hsymm : ∀ A B : C₂, (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _)
    (hcomp : ∀ (T : C₁) (M : C₃), (pfxy.app T).app M ≫ Lxy.map (T ◁ U.hom.app M) =
      c.hom.app T ▷ M ≫ (pfy.app (Lx.obj T)).app M ≫ Ly.map ((pfx.app T).app (Fy.obj M)) ≫
        c.inv.app (T ⊗ Fx.obj (Fy.obj M)))
    (M : C₃) (T : C₁) :
    leftProjection pfxy M T ≫ Lxy.map (U.hom.app M ▷ T) =
      M ◁ c.hom.app T ≫ leftProjection pfy M (Lx.obj T) ≫
        Ly.map (leftProjection pfx (Fy.obj M) T) ≫ c.inv.app (Fx.obj (Fy.obj M) ⊗ T) := by
  have hn := c.inv.naturality (β_ T (Fx.obj (Fy.obj M))).hom
  simp only [Functor.comp_map] at hn
  simp only [leftProjection, Category.assoc]
  rw [← Lxy.map_comp, ← BraidedCategory.braiding_naturality_right, Lxy.map_comp,
    reassoc_of% (hcomp T M)]
  dsimp only [Functor.comp_obj]
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Ly.map_comp_assoc (β_ (Lx.obj T) (Fy.obj M)).hom (β_ (Fy.obj M) (Lx.obj T)).hom, hsymm,
    Ly.map_id, Category.id_comp, ← BraidedCategory.braiding_naturality_right_assoc]

section Unit

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (G : D ⥤ C) [G.Monoidal] {Lg Sg : C ⥤ D}
  (adj : G ⊣ Sg) (σ : Lg ≅ Sg)
  (pf : curriedTensorInsertFunctor₁ Lg ⟶ curriedTensorPost Lg ⋙
    (Functor.whiskeringLeft D C D).obj G)

/-- **The left projection morphism of the unit point**: if `G ⊣ S` with `L ≅ S`, the projection
morphism of `L` is adjoint to the counit (`hcounit`), `G` is braided and `C` is symmetric, then
the left projection morphism after the point `𝟙 ⟶ S G 𝟙 ≅ S 𝟙 ≅ L 𝟙` is the unit of `G ⊣ S`. -/
lemma leftProjection_unit
    (hcounit : ∀ (T : C) (M : D), G.map ((pf.app T).app M) ≫
        (adj.ofNatIsoRight σ.symm).counit.app (T ⊗ G.obj M) =
      Functor.OplaxMonoidal.δ G (Lg.obj T) M ≫ (adj.ofNatIsoRight σ.symm).counit.app T ▷ G.obj M)
    (hbraid : ∀ A B : D, G.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ G B A =
      Functor.OplaxMonoidal.δ G A B ≫ (β_ (G.obj A) (G.obj B)).hom)
    (hsymm : ∀ A B : C, (β_ A B).hom ≫ (β_ B A).hom = 𝟙 _) (M : D) :
    M ◁ (adj.unit.app (𝟙_ D) ≫ Sg.map (Functor.Monoidal.εIso G).inv ≫ σ.inv.app (𝟙_ C)) ≫
        leftProjection pf M (𝟙_ C) =
      (ρ_ M).hom ≫ adj.unit.app M ≫ σ.inv.app (G.obj M) ≫ Lg.map (ρ_ (G.obj M)).inv := by
  apply ((adj.ofNatIsoRight σ.symm).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hLP : ∀ T : C, G.map (leftProjection pf M T) ≫
      (adj.ofNatIsoRight σ.symm).counit.app (G.obj M ⊗ T) =
      Functor.OplaxMonoidal.δ G M (Lg.obj T) ≫ G.obj M ◁
          (adj.ofNatIsoRight σ.symm).counit.app T := by
    intro T
    have hn := (adj.ofNatIsoRight σ.symm).counit.naturality (β_ T (G.obj M)).hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    simp only [leftProjection, Functor.map_comp, Category.assoc]
    rw [hn, reassoc_of% (hcounit T M), reassoc_of% (hbraid M (Lg.obj T)),
      ← BraidedCategory.braiding_naturality_right_assoc, hsymm, Category.comp_id]
  have hε : ∀ N, (adj.ofNatIsoRight σ.symm).counit.app N =
      G.map (σ.hom.app N) ≫ adj.counit.app N := by
    intro N
    simp [Adjunction.ofNatIsoRight]
  have hx : G.map (adj.unit.app (𝟙_ D) ≫ Sg.map (Functor.Monoidal.εIso G).inv ≫
      σ.inv.app (𝟙_ C)) ≫ (adj.ofNatIsoRight σ.symm).counit.app (𝟙_ C) =
      (Functor.Monoidal.εIso G).inv := by
    rw [hε, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      ← G.map_comp_assoc (σ.inv.app _), Iso.inv_hom_id_app, G.map_id, Category.id_comp,
      ]
    simp
  rw [hLP, ← Functor.OplaxMonoidal.δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp, hx,
    Adjunction.counit_naturality, hε]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc (σ.inv.app _), Iso.inv_hom_id_app, G.map_id, Category.id_comp,
    adj.left_triangle_components_assoc, ← cancel_mono (ρ_ (G.obj M)).hom]
  simp

end Unit

end CategoryTheory.Verdier
