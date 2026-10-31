/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # Geometric coherence from normalized supported comparisons -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory

private theorem supportedMap_ext
    {A B : Type*} [Category A] [Category B] (E : A ⥤ B) [E.Full]
    (R : B ⥤ A) (rho : E ⋙ R ≅ 𝟭 A) {M N : A} {Z : B}
    (e : Z ≅ E.obj M) (f g : Z ⟶ E.obj N) (h : R.map f = R.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  let f' := E.preimage (e.inv ≫ f)
  let g' := E.preimage (e.inv ≫ g)
  have hh : R.map (E.map f') = R.map (E.map g') := by
    simp only [f', g', E.map_preimage, Functor.map_comp, h]
  have hn := rho.hom.naturality f'
  have hm := rho.hom.naturality g'
  simp only [Functor.comp_map, Functor.id_map] at hn hm
  have hfg : f' = g' := by
    apply (cancel_epi (rho.hom.app M)).mp
    exact hn.symm.trans ((congrArg (fun z ↦ z ≫ rho.hom.app N) hh).trans hm)
  simpa only [f', g', E.map_preimage] using congrArg E.map hfg

-- A single coefficient square is enough; no coefficient-tower coherence is used.
/-- Individually normalized supported comparisons respect geometric composition.

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md, (2), the restriction
normalization argument for locally closed extension.
(blueprint: lem-sfb-normalized-extension-comparison-composition).

Proof: fullness of H' and its invertible restriction make U' faithful on maps between
supported objects. Both paths have source isomorphic to an H'-image, so it suffices
to compare their U'-images. Postcompose with the invertible rhoH'. Apply the three
individual comparison normalizations, the two restriction-compositor equations and
naturality. The remaining equality is exactly hq, the inverse pullback-square
composition equation. No faithfulness of U' away from the supported images is used. -/
theorem normalizedExtensionComparison_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (F : A₁ ⥤ A₂) (G : A₀ ⥤ A₁) (H : A₀ ⥤ A₂)
    (F' : B₁ ⥤ B₂) (G' : B₀ ⥤ B₁) (H' : B₀ ⥤ B₂) [H'.Full]
    (R : A₂ ⥤ A₁) (S : A₁ ⥤ A₀) (U : A₂ ⥤ A₀)
    (R' : B₂ ⥤ B₁) (S' : B₁ ⥤ B₀) (U' : B₂ ⥤ B₀)
    (rhoF : F ⋙ R ≅ 𝟭 A₁) (rhoG : G ⋙ S ≅ 𝟭 A₀) (rhoH : H ⋙ U ≅ 𝟭 A₀)
    (rhoF' : F' ⋙ R' ≅ 𝟭 B₁) (rhoG' : G' ⋙ S' ≅ 𝟭 B₀)
    (rhoH' : H' ⋙ U' ≅ 𝟭 B₀)
    (gamma : G ⋙ F ≅ H) (gamma' : G' ⋙ F' ≅ H')
    (c : U ≅ R ⋙ S) (c' : U' ≅ R' ⋙ S')
    (T₀ : A₀ ⥤ B₀) (T₁ : A₁ ⥤ B₁) (T₂ : A₂ ⥤ B₂)
    (qF : T₂ ⋙ R' ≅ R ⋙ T₁) (qG : T₁ ⋙ S' ≅ S ⋙ T₀)
    (qH : T₂ ⋙ U' ≅ U ⋙ T₀)
    (bF : F ⋙ T₂ ≅ T₁ ⋙ F') (bG : G ⋙ T₁ ≅ T₀ ⋙ G')
    (bH : H ⋙ T₂ ≅ T₀ ⋙ H')
    (nF : ∀ M, R'.map (bF.hom.app M) ≫ rhoF'.hom.app (T₁.obj M) =
      qF.hom.app (F.obj M) ≫ T₁.map (rhoF.hom.app M))
    (nG : ∀ M, S'.map (bG.hom.app M) ≫ rhoG'.hom.app (T₀.obj M) =
      qG.hom.app (G.obj M) ≫ T₀.map (rhoG.hom.app M))
    (nH : ∀ M, U'.map (bH.hom.app M) ≫ rhoH'.hom.app (T₀.obj M) =
      qH.hom.app (H.obj M) ≫ T₀.map (rhoH.hom.app M))
    (r : ∀ M, U.map (gamma.hom.app M) ≫ rhoH.hom.app M =
      c.hom.app (F.obj (G.obj M)) ≫ S.map (rhoF.hom.app (G.obj M)) ≫ rhoG.hom.app M)
    (r' : ∀ M, U'.map (gamma'.hom.app M) ≫ rhoH'.hom.app M =
      c'.hom.app (F'.obj (G'.obj M)) ≫ S'.map (rhoF'.hom.app (G'.obj M)) ≫
        rhoG'.hom.app M)
    (hq : ∀ K, c'.hom.app (T₂.obj K) ≫ S'.map (qF.hom.app K) ≫
      qG.hom.app (R.obj K) = qH.hom.app K ≫ T₀.map (c.hom.app K))
    (M : A₀) :
    T₂.map (gamma.hom.app M) ≫ bH.hom.app M =
      bF.hom.app (G.obj M) ≫ F'.map (bG.hom.app M) ≫ gamma'.hom.app (T₀.obj M) := by
  let e : T₂.obj (F.obj (G.obj M)) ≅ H'.obj (T₀.obj M) :=
    T₂.mapIso (gamma.app M) ≪≫ bH.app M
  apply supportedMap_ext H' U' rhoH' e
  apply (cancel_mono (rhoH'.hom.app (T₀.obj M))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [nH]
  have nq := qH.hom.naturality (gamma.hom.app M)
  simp only [Functor.comp_map] at nq
  rw [reassoc_of% nq, ← T₀.map_comp, r, T₀.map_comp, T₀.map_comp,
    ← Category.assoc, ← hq]
  have nc := c'.hom.naturality (bF.hom.app (G.obj M))
  have nc' := c'.hom.naturality (F'.map (bG.hom.app M))
  have nr := rhoF'.hom.naturality (bG.hom.app M)
  have ng := qG.hom.naturality (rhoF.hom.app (G.obj M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    at nc nc' nr ng
  rw [Category.assoc, Category.assoc, r', reassoc_of% nc', reassoc_of% nc]
  simp only [← S'.map_comp_assoc]
  have hr : R'.map (bF.hom.app (G.obj M)) ≫ R'.map (F'.map (bG.hom.app M)) ≫
      rhoF'.hom.app (G'.obj (T₀.obj M)) =
      qF.hom.app (F.obj (G.obj M)) ≫ T₁.map (rhoF.hom.app (G.obj M)) ≫
        bG.hom.app M := by
    rw [nr, ← Category.assoc, nF, Category.assoc]
  rw [hr, S'.map_comp, S'.map_comp]
  simp only [Category.assoc]
  rw [nG, reassoc_of% ng]

end CategoryTheory
