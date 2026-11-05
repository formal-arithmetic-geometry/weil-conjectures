/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Associativity of the projection map

Let `adj : F ⊣ G` be an adjunction between monoidal categories whose left adjoint `F` is
oplax monoidal, and let `PF : G M ⊗ L ⟶ G (M ⊗ F L)` be the right adjoint projection map
(`CategoryTheory.Adjunction.rightAdjointProjectionMap` for the comonoidal structure of `F`).
The projection map is compatible with the associators:
```
G M ⊗ (L ⊗ L') --PF--> G (M ⊗ F (L ⊗ L')) --G(M ◁ δ)--> G (M ⊗ (F L ⊗ F L'))
      |                                                         |
     α⁻¹                                                      G(α⁻¹)
      v                                                         v
(G M ⊗ L) ⊗ L' --PF ▷ L'--> G (M ⊗ F L) ⊗ L' --PF--> G ((M ⊗ F L) ⊗ F L')
```

## Main results

- `CategoryTheory.Adjunction.rightAdjointProjectionMap_assoc`
- `CategoryTheory.Adjunction.projectionMap_assoc`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

section LeftAdjoint

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (G' : D ⥤ C) [G'.LaxMonoidal]
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj (curriedTensor C) ⟶
    (Functor.postcompose₂.obj G).obj (curriedTensor D))

/-- The projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` is compatible with the associators, provided
the comparison `δ : G X ⊗ G' M ⟶ G (X ⊗ M)` is compatible with the lax monoidal structure of
`G'`. -/
lemma projectionMap_assoc
    (hδ : ∀ (X : D) (M M' : D), (α_ (G.obj X) (G'.obj M) (G'.obj M')).hom ≫
      G.obj X ◁ Functor.LaxMonoidal.μ G' M M' ≫ (δ.app X).app (M ⊗ M') ≫
        G.map (α_ X M M').inv = (δ.app X).app M ▷ G'.obj M' ≫ (δ.app (X ⊗ M)).app M')
    (K : C) (M M' : D) :
    F.map (α_ K (G'.obj M) (G'.obj M')).hom ≫ F.map (K ◁ Functor.LaxMonoidal.μ G' M M') ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app (M ⊗ M') ≫
          (α_ (F.obj K) M M').inv =
      ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app (K ⊗ G'.obj M)).app M' ≫
        ((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ M' := by
  apply (adj.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp]
  rw [adj.unit_naturality_assoc, adj.unit_naturality_assoc]
  have h₁ := adj.unit_app_comp_map_projectionMap_app_app_assoc G' (curriedTensor C)
    (curriedTensor D) δ K (M ⊗ M') (G.map (α_ (F.obj K) M M').inv)
  have h₂ := adj.unit_app_comp_map_projectionMap_app_app_assoc G' (curriedTensor C)
    (curriedTensor D) δ (K ⊗ G'.obj M) M'
    (G.map (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M ▷ M'))
  dsimp [projectionMapTranspose] at h₁ h₂
  rw [h₁, h₂]
  have h₃ := congr_app (δ.naturality
    (((adj.projectionMap G' (curriedTensor C) (curriedTensor D) δ).app K).app M)) M'
  have h₄ := adj.unit_app_comp_map_projectionMap_app_app G' (curriedTensor C)
    (curriedTensor D) δ K M
  dsimp [projectionMapTranspose] at h₃ h₄
  simp only [Category.assoc]
  rw [← h₃, ← comp_whiskerRight_assoc, h₄, comp_whiskerRight_assoc, ← hδ,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]

end LeftAdjoint

end CategoryTheory.Adjunction
