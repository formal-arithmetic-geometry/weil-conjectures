/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The projection map and tensor products in the second variable

Let `adj : F ⊣ G` be an adjunction between monoidal categories, with `F : D ⥤ C` a monoidal
functor, and let `π_{M, L} : G M ⊗ L ⟶ G (M ⊗ F L)` be the right adjoint projection map built
from the comonoidal structure `δ` of `F`. Then `π` is compatible with tensor products in `L`:
```
(G M ⊗ L) ⊗ N --π ▷ N--> G (M ⊗ F L) ⊗ N --π--> G ((M ⊗ F L) ⊗ F N)
      |                                                   ‖
      α                                                   ‖
      v                                                   ‖
G M ⊗ (L ⊗ N) --π--> G (M ⊗ F (L ⊗ N)) --G(M ◁ δ)--> G (M ⊗ (F L ⊗ F N)) --G(α⁻¹)
```
(`CategoryTheory.Adjunction.rightAdjointProjectionMap_whiskerRight_comp`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- **The projection map is compatible with tensor products in the second variable.** For an
adjunction `F ⊣ G` with `F` monoidal and `φ` the comonoidal structure `δ` of `F`, the projection
map `π_{M, L} : G M ⊗ L ⟶ G (M ⊗ F L)` satisfies
`π_{M, L} ▷ N ≫ π_{M ⊗ F L, N} = α ≫ π_{M, L ⊗ N} ≫ G (M ◁ δ_{L, N} ≫ α⁻¹)`. -/
theorem rightAdjointProjectionMap_whiskerRight_comp (hφ : ∀ a b, (φ.app a).app b = δ F a b)
    (M : C) (L N : D) :
    ((adj.rightAdjointProjectionMap φ).app M).app L ▷ N ≫
        ((adj.rightAdjointProjectionMap φ).app (M ⊗ F.obj L)).app N =
      (α_ (G.obj M) L N).hom ≫ ((adj.rightAdjointProjectionMap φ).app M).app (L ⊗ N) ≫
        G.map (M ◁ δ F L N ≫ (α_ M (F.obj L) (F.obj N)).inv) := by
  apply (adj.homEquiv _ _).symm.injective
  have h₁ := adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L
  have h₂ := adj.map_rightAdjointProjectionMap_app_app_comp_counit φ (M ⊗ F.obj L) N
  have h₃ := adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M (L ⊗ N)
  rw [hφ] at h₁ h₂ h₃
  dsimp at h₁ h₂ h₃
  rw [homEquiv_counit, homEquiv_counit]
  dsimp
  simp only [Functor.map_comp, Category.assoc]
  rw [h₂, adj.counit_naturality, adj.counit_naturality_assoc, reassoc_of% h₃,
    Functor.Monoidal.map_whiskerRight_assoc, Functor.Monoidal.μ_δ_assoc,
    ← comp_whiskerRight, h₁, Functor.Monoidal.map_associator]
  simp only [Category.assoc, comp_whiskerRight]
  rw [Functor.Monoidal.μ_δ_assoc, ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.Monoidal.μ_δ, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← associator_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open _root_.CategoryTheory.Functor

section LeftAdjoint

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C) [G'.Monoidal]
  (δ : (((whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
    (postcompose₂.obj G).obj (curriedTensor D))

/-- **The left adjoint projection map is compatible with tensor products in the second
variable.** Let `adj : F ⊣ G`, let `G'` be monoidal and let `δ : G X ⊗ G' Y ⟶ G (X ⊗ Y)` be
compatible with the monoidal structure of `G'` (hypothesis `hδ`). Then the projection map
`p_{K, M} : F (K ⊗ G' M) ⟶ F K ⊗ M` satisfies
`p_{K, M ⊗ N} = F (K ◁ δ_{G'} ≫ α⁻¹) ≫ p_{K ⊗ G' M, N} ≫ p_{K, M} ▷ N ≫ α`. -/
theorem projectionMap_app_app_tensorObj
    (hδ : ∀ X Y Z, (δ.app X).app (Y ⊗ Z) =
      G.obj X ◁ OplaxMonoidal.δ G' Y Z ≫ (α_ _ _ _).inv ≫ (δ.app X).app Y ▷ G'.obj Z ≫
        (δ.app (X ⊗ Y)).app Z ≫ G.map (α_ X Y Z).hom)
    (K : C) (M N : D) :
    ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app (M ⊗ N) =
      F.map (K ◁ OplaxMonoidal.δ G' M N ≫ (α_ K (G'.obj M) (G'.obj N)).inv) ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app
          (K ⊗ G'.obj M)).app N ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ N ≫
        (α_ (F.obj K) M N).hom := by
  apply (adj.homEquiv _ _).injective
  have h₁ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C) (curriedTensor D)
    δ K M
  have h₂ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C) (curriedTensor D)
    δ (K ⊗ G'.obj M) N
  have h₃ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C) (curriedTensor D)
    δ K (M ⊗ N)
  dsimp at h₁ h₂ h₃
  rw [homEquiv_unit, homEquiv_unit]
  dsimp
  rw [h₃]
  simp only [Functor.map_comp, Category.assoc]
  rw [adj.unit_naturality_assoc, adj.unit_naturality_assoc, reassoc_of% h₂]
  dsimp [projectionMapTranspose] at h₁ ⊢
  have hn : (δ.app (F.obj (K ⊗ G'.obj M))).app N ≫
      G.map (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ N) =
      G.map (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M) ▷
        G'.obj N ≫ (δ.app (F.obj K ⊗ M)).app N := by
    have := NatTrans.congr_app (δ.naturality
      (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M)) N
    dsimp at this
    exact this.symm
  rw [Category.assoc, reassoc_of% hn, ← comp_whiskerRight_assoc, h₁, hδ, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left_assoc]

end LeftAdjoint

end CategoryTheory.Adjunction
