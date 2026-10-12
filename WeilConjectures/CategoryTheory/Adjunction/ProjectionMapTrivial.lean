/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The projection map of an adjunction whose functors are trivialised

Let `adj : F ⊣ G` be an adjunction of endofunctors of `C`, `T : C ⥤ C ⥤ C` a bifunctor
(written `⊗`), `G' : C ⥤ C` and `δ : G K ⊗ G' M ⟶ G (K ⊗ M)` a comparison, so that the
projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` (`CategoryTheory.Adjunction.projectionMap`) is
defined. Suppose given trivialisations `ι : F ⟶ 𝟭`, `u : 𝟭 ⟶ G` and `λ : G' ⟶ 𝟭` such that
the unit of `adj` followed by `G ι` is `u`, and `δ` becomes `1 ⊗ λ` under `u`. Then the
projection map becomes `1 ⊗ λ` under `ι`
(`CategoryTheory.Adjunction.projectionMap_app_app_comp_map_of_trivial`). This applies for
instance to the extension by zero along the identity of a scheme.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category* C] {F G : C ⥤ C} (adj : F ⊣ G) (G' : C ⥤ C) (T : C ⥤ C ⥤ C)
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj T ⟶ (Functor.postcompose₂.obj G).obj T)
  (ι : F ⟶ 𝟭 C) (u : 𝟭 C ⟶ G) (l : G' ⟶ 𝟭 C)

/-- **The projection map of a trivialised adjunction**: if `η_K ≫ G ι_K = u_K` and
`(u_K ⊗ 1) ≫ δ_{K,M} = (1 ⊗ λ_M) ≫ u_{K ⊗ M}`, then the square
```
F (K ⊗ G' M) --projection--> F K ⊗ M
     |                          |
F (1 ⊗ λ)                     ι ⊗ 1
     v                          v
F (K ⊗ M) ------ι-------->   K ⊗ M
```
commutes. -/
lemma projectionMap_app_app_comp_map_of_trivial
    (hu : ∀ K, adj.unit.app K ≫ G.map (ι.app K) = u.app K)
    (hδ : ∀ K M, (T.map (u.app K)).app (G'.obj M) ≫ (δ.app K).app M =
      (T.obj K).map (l.app M) ≫ u.app ((T.obj K).obj M))
    (K M : C) :
    ((adj.projectionMap G' T T δ).app K).app M ≫ (T.map (ι.app K)).app M =
      F.map ((T.obj K).map (l.app M)) ≫ ι.app ((T.obj K).obj M) := by
  apply (adj.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp]
  rw [unit_app_comp_map_projectionMap_app_app_assoc]
  have h₁ := adj.unit.naturality_assoc ((T.obj K).map (l.app M)) (G.map (ι.app _))
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h₁
  rw [← h₁, hu, ← hδ, ← hu]
  have h₂ := NatTrans.congr_app (δ.naturality (ι.app K)) M
  dsimp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskeringLeft₂,
    Functor.postcompose₂, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
    Functor.comp_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app] at h₂ ⊢
  rw [← NatTrans.comp_app_assoc, ← T.map_comp, ← h₂]
  simp only [projectionMapTranspose, NatTrans.comp_app, Category.assoc, T.map_comp]
  rfl

end CategoryTheory.Adjunction
