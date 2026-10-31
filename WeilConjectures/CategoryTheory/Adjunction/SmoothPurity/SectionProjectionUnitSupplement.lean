/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.UnitComparison
public import WeilConjectures.CategoryTheory.SectionProjectionUnit

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-section-projection-unit).

# Projection cancellation along a section

Source: blueprint thm-amb-p1-adjunction.proof.md, contraction along the diagonal section.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

attribute [local implicit_reducible] TwoSquare

/-- Compose tensor comparisons and cancel a section compositor. -/
theorem tensor_compatibility_of_composite_section
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ C)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (dH : (Functor.postcompose₂.obj H).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C).obj H).obj H).obj (curriedTensor C))
    (c : H ≅ F ⋙ G) (i : H ≅ 𝟭 C) (M N : C)
    (hc : (dH.app M).app N ≫ (c.hom.app M ⊗ₘ c.hom.app N) =
      c.hom.app (M ⊗ N) ≫ G.map ((dF.app M).app N) ≫
        (dG.app (F.obj M)).app (F.obj N))
    (hi : (dH.app M).app N ≫ (i.hom.app M ⊗ₘ i.hom.app N) =
      i.hom.app (M ⊗ N)) :
    G.map ((dF.app M).app N) ≫ (dG.app (F.obj M)).app (F.obj N) ≫
      ((c.symm ≪≫ i).hom.app M ⊗ₘ (c.symm ≪≫ i).hom.app N) =
      (c.symm ≪≫ i).hom.app (M ⊗ N) := by
  apply (cancel_epi (c.hom.app (M ⊗ N))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% hc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  exact hi

/-- Convert the inverse-unit form of a pullback law to its direct form. -/
theorem unit_law_of_inverse
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {X' Y' : D} (e : X ≅ Y) (e' : X' ≅ Y')
    (m : F.obj X ⟶ X') (n : F.obj Y ⟶ Y')
    (h : F.map e.inv ≫ m = n ≫ e'.inv) :
    m ≫ e'.hom = F.map e.hom ≫ n := by
  apply (cancel_epi (F.map e.inv)).mp
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- Tensor evaluation commutes with a square once its projection and scalar trace do. -/
theorem tensor_evaluation_baseChange
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D') (σ : U ⋙ F' ≅ F ⋙ V)
    (ex : R ⋙ U ⟶ V ⋙ R')
    (p : R ⋙ (curriedTensor C).flip ⟶
      (Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj F).obj (curriedTensor D).flip))
    (p' : R' ⋙ (curriedTensor C').flip ⟶
      (Functor.postcompose₂.obj R').obj
        ((((Functor.whiskeringLeft₂ D').obj (𝟭 D')).obj F').obj (curriedTensor D').flip))
    (dU : (Functor.postcompose₂.obj U).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C').obj U).obj U).obj (curriedTensor C'))
    (dV : (Functor.postcompose₂.obj V).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ D').obj V).obj V).obj (curriedTensor D'))
    (eU : U.obj (𝟙_ C) ⟶ 𝟙_ C')
    (L : D) (L' : D') (c : V.obj L ≅ L')
    (τ : R.obj L ⟶ 𝟙_ C) (τ' : R'.obj L' ⟶ 𝟙_ C')
    (ht : U.map τ ≫ eU = ex.app L ≫ R'.map c.hom ≫ τ')
    (K : C)
    (hp : U.map ((p.app L).app K) ≫ ex.app (F.obj K ⊗ L) ≫
        R'.map ((dV.app (F.obj K)).app L) =
      (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        (p'.app (V.obj L)).app (U.obj K) ≫
          R'.map (σ.hom.app K ▷ V.obj L))
    (hu : (dU.app K).app (𝟙_ C) ≫ U.obj K ◁ eU ≫ (ρ_ (U.obj K)).hom =
      U.map (ρ_ K).hom)
    [IsIso ((p.app L).app K)] [IsIso ((p'.app L').app (U.obj K))] :
    U.map (inv ((p.app L).app K) ≫ K ◁ τ ≫ (ρ_ K).hom) =
      ex.app (F.obj K ⊗ L) ≫
        R'.map ((dV.app (F.obj K)).app L ≫
          (σ.inv.app K ⊗ₘ c.hom)) ≫
        inv ((p'.app L').app (U.obj K)) ≫ U.obj K ◁ τ' ≫ (ρ_ (U.obj K)).hom := by
  apply (cancel_epi (U.map ((p.app L).app K))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc, IsIso.hom_inv_id, U.map_id, Category.id_comp]
  have hn := NatTrans.congr_app (p'.naturality c.hom) (U.obj K)
  change U.obj K ◁ R'.map c.hom ≫ (p'.app L').app (U.obj K) =
    (p'.app (V.obj L)).app (U.obj K) ≫ R'.map (F'.obj (U.obj K) ◁ c.hom) at hn
  have hσ : (σ.hom.app K ▷ V.obj L) ≫ (σ.inv.app K ⊗ₘ c.hom) =
      F'.obj (U.obj K) ◁ c.hom := by
    rw [tensorHom_def, ← Category.assoc, ← comp_whiskerRight,
      Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp]
    rfl
  calc
    U.map (K ◁ τ) ≫ U.map (ρ_ K).hom =
        U.map (K ◁ τ) ≫ (dU.app K).app (𝟙_ C) ≫
          U.obj K ◁ eU ≫ (ρ_ (U.obj K)).hom := by rw [hu]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ (U.map τ ≫ eU) ≫
        (ρ_ (U.obj K)).hom := by
      have h := (dU.app K).naturality τ
      change U.map (K ◁ τ) ≫ (dU.app K).app (𝟙_ C) =
        (dU.app K).app (R.obj L) ≫ U.obj K ◁ U.map τ at h
      rw [reassoc_of% h, whiskerLeft_comp, Category.assoc]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        U.obj K ◁ R'.map c.hom ≫ U.obj K ◁ τ' ≫ (ρ_ (U.obj K)).hom := by
      rw [ht]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        (p'.app (V.obj L)).app (U.obj K) ≫
        R'.map (F'.obj (U.obj K) ◁ c.hom) ≫
        inv ((p'.app L').app (U.obj K)) ≫
        U.obj K ◁ τ' ≫ (ρ_ (U.obj K)).hom := by
      rw [← reassoc_of% hn, IsIso.hom_inv_id_assoc]
    _ = _ := by
      rw [← hσ, R'.map_comp]
      simp only [Category.assoc]
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ R'.map (σ.inv.app K ⊗ₘ c.hom) ≫
        inv ((p'.app L').app (U.obj K)) ≫
          U.obj K ◁ τ' ≫ (ρ_ (U.obj K)).hom) hp.symm

private theorem projection_conjugate_at
    {C D : Type*} [Category C] [Category D]
    {F F' : D ⥤ C} {G G' : C ⥤ D} (adj : F ⊣ G) (adj' : F' ⊣ G')
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    (φ : (Functor.postcompose₂.obj F).obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T_C)
    (φ' : (Functor.postcompose₂.obj F').obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F').obj F').obj T_C)
    (α : F' ⟶ F) (M : C) (L : D)
    (hα : α.app ((T_D.obj (G.obj M)).obj L) ≫ (φ.app (G.obj M)).app L =
      (φ'.app (G.obj M)).app L ≫
        (T_C.map (α.app (G.obj M))).app (F'.obj L) ≫
        (T_C.obj (F.obj (G.obj M))).map (α.app L)) :
    (T_D.map ((conjugateEquiv adj adj' α).app M)).app L ≫
        ((adj'.rightAdjointProjectionMap φ').app M).app L ≫
        G'.map ((T_C.obj M).map (α.app L)) =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫
        (conjugateEquiv adj adj' α).app ((T_C.obj M).obj (F.obj L)) := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    adj'.counit_naturality, conjugateEquiv_counit]
  erw [Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  erw [α.naturality_assoc]
  erw [adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L]
  have h₁ := NatTrans.congr_app
    (φ'.naturality ((conjugateEquiv adj adj' α).app M)) L
  dsimp at h₁ ⊢
  rw [reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← T_C.map_comp,
    conjugateEquiv_counit, reassoc_of% hα, T_C.map_comp, NatTrans.comp_app]
  erw [(T_C.map (adj.counit.app M)).naturality (α.app L)]
  simp only [Category.assoc]
  rfl

/-- The projection map for two adjunctions, normalized by a section comparison.
Only tensor compatibility at the chosen second coefficient is needed. -/
private theorem section_projection_composite
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M N : C)
    (hl : G.map ((dF.app M).app N) ≫
      (dG.app (F.obj M)).app (F.obj N) ≫
        (l.hom.app M ⊗ₘ l.hom.app N) = l.hom.app (M ⊗ N)) :
    let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
    let pF := adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)
    let pG := adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)
    M ◁ t.inv.app N ≫ (pF.app (S.obj N)).app M ≫
      R.map ((pG.app N).app (F.obj M)) ≫
      t.hom.app (G.obj (F.obj M) ⊗ N) ≫ l.hom.app M ▷ N = 𝟙 (M ⊗ N) := by
  let d : (Functor.postcompose₂.obj (F ⋙ G)).obj (curriedTensor C).flip ⟶
      (((Functor.whiskeringLeft₂ C).obj (F ⋙ G)).obj (F ⋙ G)).obj
        (curriedTensor C).flip :=
    (flipFunctor _ _ _).map
      ((Functor.postcompose₂.obj G).map dF ≫
        (((Functor.whiskeringLeft₂ C).obj F).obj F).map dG)
  let e : (Functor.postcompose₂.obj (𝟭 C)).obj (curriedTensor C).flip ⟶
      (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj (𝟭 C)).obj
        (curriedTensor C).flip := 𝟙 _
  have he (A B : C) :
      ((Adjunction.id.rightAdjointProjectionMap e).app A).app B = 𝟙 (B ⊗ A) := by
    have hh : ((Adjunction.id : 𝟭 C ⊣ 𝟭 C).homEquiv (B ⊗ A) (B ⊗ A))
        (𝟙 (B ⊗ A)) = 𝟙 (B ⊗ A) := Adjunction.homEquiv_id _ _
    simpa [Adjunction.rightAdjointProjectionMap, e] using hh
  have hc := projection_conjugate_at Adjunction.id (adj.comp adj')
    e d l.hom N M (by
      simpa [d, e, tensorHom_def', Category.assoc] using hl.symm)
  dsimp only [Functor.id_map, Functor.id_obj] at hc
  rw [he] at hc
  have hp := adj.rightAdjointProjectionMap_comp adj'
    (T₁ := (curriedTensor D).flip) (S₁ := (curriedTensor C).flip)
    (T_B := (curriedTensor C).flip)
    ((flipFunctor _ _ _).map dF) ((flipFunctor _ _ _).map dG) d
    (fun _ _ ↦ rfl) N M
  rw [hp] at hc
  dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map] at hc
  dsimp only
  have ht : conjugateEquiv Adjunction.id (adj.comp adj') l.hom =
      (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).inv := by
    rfl
  rw [ht] at hc
  have hn := (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).hom.naturality
    (l.hom.app M ▷ N)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.comp_obj, Functor.id_obj] at hn
  simp only [Category.assoc] at hc ⊢
  rw [← hn]
  have hc' := congrArg
    (fun f ↦ f ≫ (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).hom.app
      (M ⊗ N)) hc
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, Functor.comp_map,
    Category.assoc, Category.id_comp, Iso.inv_hom_id_app,
    Functor.flip_map_app, curriedTensor_obj_map, Functor.id_obj] using hc'

/-- Two ordered projection maps along a section cancel against the conjugate
composition comparison and the right unitors.
Source: blueprint thm-amb-p1-adjunction.proof.md, diagonal contraction.
Proof: the projection map of a composite is the composite of the projection maps.
Conjugate its adjunction to the identity using the section isomorphism. Tensor
compatibility identifies its projection with the identity. Naturality of the
conjugate comparison and of the right unitor gives the displayed equation. -/
theorem section_projection_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M : C)
    (hl : G.map ((dF.app M).app (𝟙_ C)) ≫
      (dG.app (F.obj M)).app (F.obj (𝟙_ C)) ≫
        (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C)) :
    let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
    let pF := adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)
    let pG := adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)
    (ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ (pF.app (S.obj (𝟙_ C))).app M ≫
      R.map ((pG.app (𝟙_ C)).app (F.obj M) ≫
        S.map (l.hom.app M ▷ (𝟙_ C) ≫ (ρ_ M).hom)) ≫ t.hom.app M = 𝟙 M := by
  have hc := section_projection_composite adj adj' dF dG l M (𝟙_ C) hl
  let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
  have hn := t.hom.naturality (l.hom.app M ▷ (𝟙_ C) ≫ (ρ_ M).hom)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hn
  dsimp only
  rw [R.map_comp]
  simp only [Category.assoc]
  rw [hn]
  have hc' := congrArg (fun f ↦ (ρ_ M).inv ≫ f ≫ (ρ_ M).hom) hc
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id, t, Functor.comp_obj] using hc'

/-- Invert the normalized section projection word. -/
theorem section_projection_inverse
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {S : C ⥤ D} (R : D ⥤ C) (t : S ⋙ R ≅ 𝟭 C) (M : C) (V : D)
    (p : M ⊗ R.obj (S.obj (𝟙_ C)) ⟶ R.obj V) (q : V ⟶ S.obj M)
    [IsIso p] [IsIso q]
    (h : (ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ p ≫ R.map q ≫
      t.hom.app M = 𝟙 M) :
    t.inv.app M ≫ R.map (inv q) ≫ inv p ≫
      M ◁ t.hom.app (𝟙_ C) ≫ (ρ_ M).hom = 𝟙 M := by
  have he : asIso ((ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ p ≫ R.map q ≫
      t.hom.app M) = Iso.refl M := Iso.ext h
  have hc := congrArg Iso.inv he
  simpa only [asIso_inv, Iso.refl_inv, IsIso.inv_comp, IsIso.Iso.inv_hom,
    IsIso.inv_id, IsIso.Iso.inv_inv, NatIso.inv_hom_app, NatIso.inv_inv_app,
    ← Functor.map_inv, inv_whiskerLeft,
    Category.assoc] using hc

/-- A scalar section integral remains the identity after tensoring an arbitrary object.
Source: blueprint thm-amb-p1-adjunction.proof.md, both diagonal contractions.
Proof: inverse projection naturality moves the supported class outside the inverse
projection. Its scalar integral is the section comparison. The normalized inverse
section-projection equation then gives identity. -/
theorem section_integral_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] {F : C ⥤ D} {R : D ⥤ C} {S : C ⥤ D}
    (t : S ⋙ R ≅ 𝟭 C) (M : C) (V : D)
    (p : M ⊗ R.obj (S.obj (𝟙_ C)) ⟶ R.obj (F.obj M ⊗ S.obj (𝟙_ C)))
    (pV : M ⊗ R.obj V ⟶ R.obj (F.obj M ⊗ V))
    (q : F.obj M ⊗ S.obj (𝟙_ C) ⟶ S.obj M)
    [IsIso p] [IsIso pV] [IsIso q]
    (δ : S.obj (𝟙_ C) ⟶ V) (τ : R.obj V ⟶ 𝟙_ C)
    (hp : p ≫ R.map (F.obj M ◁ δ) = (M ◁ R.map δ) ≫ pV)
    (hδ : t.inv.app (𝟙_ C) ≫ R.map δ ≫ τ = 𝟙 (𝟙_ C))
    (h : t.inv.app M ≫ R.map (inv q) ≫ inv p ≫
      M ◁ t.hom.app (𝟙_ C) ≫ (ρ_ M).hom = 𝟙 M) :
    t.inv.app M ≫ R.map (inv q) ≫ R.map (F.obj M ◁ δ) ≫
      inv pV ≫ M ◁ τ ≫ (ρ_ M).hom = 𝟙 M := by
  have hn : R.map (F.obj M ◁ δ) ≫ inv pV = inv p ≫ M ◁ R.map δ := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [IsIso.hom_inv_id_assoc]
  have hτ : R.map δ ≫ τ = t.hom.app (𝟙_ C) := by
    apply (cancel_epi (t.inv.app (𝟙_ C))).mp
    rw [hδ, Iso.inv_hom_id_app]
    rfl
  rw [reassoc_of% hn, ← whiskerLeft_comp_assoc, hτ]
  exact h

/-- Transport of a left adjoint along its own comparison induces identity on the right. -/
theorem conjugate_ofNatIsoLeft
    {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (e : L ≅ L') :
    conjugateEquiv adj (adj.ofNatIsoLeft e) e.inv = 𝟙 R := by
  ext X
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    ← Functor.map_comp, Category.assoc]

/-- The reverse comparison also induces identity on the unchanged right adjoint. -/
theorem conjugate_ofNatIsoLeft_reverse
    {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (e : L ≅ L') :
    conjugateEquiv (adj.ofNatIsoLeft e) adj e.hom = 𝟙 R := by
  ext X
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit, ← Functor.map_comp]

/-- Inverting two compatible presentations of a section projection cancels their
coordinate comparison. -/
theorem inverse_section_projection
    {C : Type*} [Category C] {U V W : C}
    (q : U ⟶ W) (q' : V ⟶ W) [IsIso q] [IsIso q']
    (c : U ⟶ V) (h : c ≫ q' = q) : inv q ≫ c = inv q' := by
  apply (cancel_mono q').mp
  rw [Category.assoc, h, IsIso.inv_hom_id, IsIso.inv_hom_id]

/-- Conjugation is unchanged by reassociating a composite adjunction. -/
theorem conjugate_assoc_left
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {L' : D ⥤ E} {R' : E ⥤ D} (b : L' ⊣ R')
    {L'' : E ⥤ F} {R'' : F ⥤ E} (c : L'' ⊣ R'')
    {K : C ⥤ F} {S : F ⥤ C} (d : K ⊣ S)
    (x : K ⟶ L ⋙ L' ⋙ L'') :
    conjugateEquiv (a.comp (b.comp c)) d x =
      conjugateEquiv ((a.comp b).comp c) d x := by
  have h := conjugateEquiv_comp (a.comp (b.comp c)) ((a.comp b).comp c) d
    (Functor.associator L L' L'').hom x
  rw [conjugateEquiv_associator_hom] at h
  have hx : x ≫ (Functor.associator L L' L'').hom = x := by
    ext M
    simp
  rw [hx] at h
  ext M
  have hm := congr_app h M
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id] using hm.symm

end CategoryTheory.Adjunction
