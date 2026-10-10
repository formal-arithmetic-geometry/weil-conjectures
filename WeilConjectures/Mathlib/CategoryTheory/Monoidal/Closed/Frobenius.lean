/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Frobenius maps and localization

Let `adj : G ⊣ F` be an adjunction whose right adjoint `F` is monoidal, and let `adj' : G' ⊣ F'`
be an adjunction "induced" by `adj` along lax monoidal functors `L₁ : C₁ ⥤ D₁` and
`L₂ : C₂ ⥤ D₂` (typically localization functors): there are isomorphisms
`F ⋙ L₁ ≅ L₂ ⋙ F'` and `G ⋙ L₂ ≅ L₁ ⋙ G'` compatible with the units of the adjunctions and
with the comonoidal structures of `F` and `F'`. We show that the Frobenius map of `adj'` at
`(L₂ K, L₁ M)` is an isomorphism as soon as the Frobenius map of `adj` at `(K, M)` is, provided
that the relevant lax monoidal structure maps of `L₁` and `L₂` are isomorphisms
(`CategoryTheory.Adjunction.isIso_frobeniusMap_obj_of_isIso_frobeniusMap`).

We also record that being an isomorphism for the Frobenius map only depends on the isomorphism
classes of its arguments (`CategoryTheory.Adjunction.isIso_frobeniusMap_of_iso`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Functor

namespace CategoryTheory

namespace Adjunction

section

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L : D ⥤ C} {F : C ⥤ D} (adj : L ⊣ F) [F.LaxMonoidal]

/-- The Frobenius map of `adj` is an isomorphism at `(K', M')` if it is an isomorphism at
isomorphic arguments `(K, M)`, by its naturality in both variables. -/
lemma isIso_frobeniusMap_of_iso {K K' : C} {M M' : D} (eK : K ≅ K') (eM : M ≅ M')
    [IsIso (adj.frobeniusMap K M)] : IsIso (adj.frobeniusMap K' M') := by
  have : IsIso (adj.frobeniusMap K M') := by
    have : IsIso (L.map (F.obj K ◁ eM.hom) ≫ adj.frobeniusMap K M') := by
      rw [adj.map_whiskerLeft_comp_frobeniusMap]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.map (F.obj K ◁ eM.hom)) _
  have : IsIso (L.map (F.map eK.hom ▷ M') ≫ adj.frobeniusMap K' M') := by
    rw [adj.map_whiskerRight_comp_frobeniusMap]
    infer_instance
  exact IsIso.of_isIso_comp_left (L.map (F.map eK.hom ▷ M')) _

end

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F) [F.Monoidal]
  {G' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁} (adj' : G' ⊣ F') [F'.Monoidal]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} [L₁.LaxMonoidal] [L₂.LaxMonoidal]
  (eF : F ⋙ L₁ ≅ L₂ ⋙ F') (eG : G ⋙ L₂ ≅ L₁ ⋙ G')

/-- If the comonoidal structures of `F` and `F'` are compatible through `eF` and the lax
monoidal structures of `L₁` and `L₂`, then so are their monoidal structures. -/
lemma μ_comp_map_μ_of_δ_comp (K N : C₂)
    (hδ : OplaxMonoidal.δ F' (L₂.obj K) (L₂.obj N) ≫ (eF.inv.app K ⊗ₘ eF.inv.app N) ≫
      LaxMonoidal.μ L₁ (F.obj K) (F.obj N) =
        F'.map (LaxMonoidal.μ L₂ K N) ≫ eF.inv.app (K ⊗ N) ≫ L₁.map (OplaxMonoidal.δ F K N)) :
    LaxMonoidal.μ F' (L₂.obj K) (L₂.obj N) ≫ F'.map (LaxMonoidal.μ L₂ K N) =
      (eF.inv.app K ⊗ₘ eF.inv.app N) ≫ LaxMonoidal.μ L₁ (F.obj K) (F.obj N) ≫
        L₁.map (LaxMonoidal.μ F K N) ≫ eF.hom.app (K ⊗ N) := by
  rw [reassoc_of% (Monoidal.μ_δ_assoc F' (L₂.obj K) (L₂.obj N) _).symm.trans
    (congrArg (LaxMonoidal.μ F' _ _ ≫ ·) hδ)]
  simp [← L₁.map_comp_assoc]

/-- **Frobenius maps and localization.** Let `adj' : G' ⊣ F'` be induced by `adj : G ⊣ F`
along `L₁` and `L₂`, compatibly with the units (`hunit`) and the comonoidal structures of `F`
and `F'` (`hδ`). If the Frobenius map of `adj` at `(K, M)` is an isomorphism, and so are the
lax monoidal structure maps `L₁ (F K) ⊗ L₁ M ⟶ L₁ (F K ⊗ M)` and
`L₂ K ⊗ L₂ (G M) ⟶ L₂ (K ⊗ G M)`, then the Frobenius map of `adj'` at `(L₂ K, L₁ M)` is an
isomorphism: up to these isomorphisms, it is the image under `L₂` of the Frobenius map of
`adj`. -/
theorem isIso_frobeniusMap_obj_of_isIso_frobeniusMap
    (hunit : ∀ M, adj'.unit.app (L₁.obj M) =
      L₁.map (adj.unit.app M) ≫ eF.hom.app (G.obj M) ≫ F'.map (eG.hom.app M))
    (hδ : ∀ K N, OplaxMonoidal.δ F' (L₂.obj K) (L₂.obj N) ≫ (eF.inv.app K ⊗ₘ eF.inv.app N) ≫
      LaxMonoidal.μ L₁ (F.obj K) (F.obj N) =
        F'.map (LaxMonoidal.μ L₂ K N) ≫ eF.inv.app (K ⊗ N) ≫ L₁.map (OplaxMonoidal.δ F K N))
    (K : C₂) (M : C₁) [IsIso (adj.frobeniusMap K M)]
    [IsIso (LaxMonoidal.μ L₁ (F.obj K) M)] [IsIso (LaxMonoidal.μ L₂ K (G.obj M))] :
    IsIso (adj'.frobeniusMap (L₂.obj K) (L₁.obj M)) := by
  have key : adj'.frobeniusMap (L₂.obj K) (L₁.obj M) ≫
      (L₂.obj K ◁ eG.inv.app M ≫ LaxMonoidal.μ L₂ K (G.obj M)) =
      (G'.map (eF.inv.app K ▷ L₁.obj M ≫ LaxMonoidal.μ L₁ (F.obj K) M) ≫
        eG.inv.app (F.obj K ⊗ M)) ≫ L₂.map (adj.frobeniusMap K M) := by
    apply (adj'.homEquiv _ _).injective
    rw [adj'.homEquiv_naturality_right, homEquiv_frobeniusMap, adj'.homEquiv_unit]
    simp only [Functor.map_comp, Category.assoc]
    rw [adj'.unit_naturality_assoc, adj'.unit_naturality_assoc, hunit, hunit]
    simp only [Category.assoc, ← F'.map_comp]
    have hn := eF.hom.naturality (adj.frobeniusMap K M)
    simp only [Functor.comp_map] at hn
    rw [Iso.hom_inv_id_app_assoc, ← hn, ← L₁.map_comp_assoc, unit_app_comp_map_frobeniusMap]
    simp only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [← LaxMonoidal.μ_natural_right_assoc L₁]
    erw [LaxMonoidal.μ_natural_right_assoc F' (L₂.obj K) (eG.hom.app M)]
    rw [← F'.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app]
    simp only [MonoidalCategory.whiskerLeft_id, F'.map_id, Category.id_comp]
    erw [μ_comp_map_μ_of_δ_comp eF K (G.obj M) (hδ _ _)]
    simp [tensorHom_def', whisker_exchange_assoc]
  have : IsIso (adj'.frobeniusMap (L₂.obj K) (L₁.obj M) ≫
      (L₂.obj K ◁ eG.inv.app M ≫ LaxMonoidal.μ L₂ K (G.obj M))) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (L₂.obj K ◁ eG.inv.app M ≫ LaxMonoidal.μ L₂ K (G.obj M))

end Adjunction

end CategoryTheory
