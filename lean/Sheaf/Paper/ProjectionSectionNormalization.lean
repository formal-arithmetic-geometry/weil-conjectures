/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.ModuleProjectionSectionInverse
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence

/-!
# Projection normalization for a proper retraction and its closed section

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), diagonal
projection identification and cancellations on p_i Delta = id
(blueprint: lem-sfb-projection-section-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [-instance] CategoryTheory.catToReflQuiver in
private def postcomposeComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : C ⥤ D) (T : A ⥤ B ⥤ C) (S : A ⥤ B ⥤ D)
    (φ : T ⋙ (Functor.whiskeringRight B C D).obj F ⟶ S) :
    (Functor.postcompose₂.obj F).obj T ⟶ S where
  app X :=
    { app := fun Y ↦ (φ.app X).app Y
      naturality := fun _ _ f ↦ (φ.app X).naturality f }
  naturality X Y f := by
    ext Z
    exact NatTrans.congr_app (φ.naturality f) Z

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
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

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_unit_compatibility
    {C : Type*} [Category C] [MonoidalCategory C]
    (H : C ⥤ C) [H.OplaxMonoidal] (l : H ≅ 𝟭 C)
    (hu : l.hom.app (𝟙_ C) = Functor.OplaxMonoidal.η H) (M : C) :
    Functor.OplaxMonoidal.δ H M (𝟙_ C) ≫
      (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C) := by
  apply (cancel_mono (ρ_ M).hom).1
  rw [hu, tensorHom_def']
  simp only [Functor.id_obj, Category.assoc]
  rw [rightUnitor_naturality]
  rw [Functor.OplaxMonoidal.right_unitality_hom_assoc]
  exact l.hom.naturality (ρ_ M).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_unit_compatibility_comp
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.OplaxMonoidal] [G.OplaxMonoidal]
    (l : F ⋙ G ≅ 𝟭 C) (M : C)
    (hu : l.hom.app (𝟙_ C) = G.map (Functor.OplaxMonoidal.η F) ≫
      Functor.OplaxMonoidal.η G) :
    G.map (Functor.OplaxMonoidal.δ F M (𝟙_ C)) ≫
      Functor.OplaxMonoidal.δ G (F.obj M) (F.obj (𝟙_ C)) ≫
        (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C) := by
  have ht := tensor_unit_compatibility (F ⋙ G) l hu M
  simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using ht

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_unit_comparison_compatibility
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.OplaxMonoidal] [G.OplaxMonoidal]
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M : C)
    (hu : l.hom.app (𝟙_ C) = G.map (Functor.OplaxMonoidal.η F) ≫
      Functor.OplaxMonoidal.η G)
    (hF : Functor.OplaxMonoidal.δ F M (𝟙_ C) = (dF.app M).app (𝟙_ C))
    (hG : Functor.OplaxMonoidal.δ G (F.obj M) (F.obj (𝟙_ C)) =
      (dG.app (F.obj M)).app (F.obj (𝟙_ C))) :
    G.map ((dF.app M).app (𝟙_ C)) ≫
      (dG.app (F.obj M)).app (F.obj (𝟙_ C)) ≫
        (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C) := by
  have ht := tensor_unit_compatibility_comp F G l M hu
  rw [hF, hG] at ht
  exact ht

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem section_projection_unit
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

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem section_projection_unit_with_maps
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
        (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C))
    (t : S ⋙ R ≅ 𝟭 C)
    (p : M ⊗ R.obj (S.obj (𝟙_ C)) ⟶ R.obj (F.obj M ⊗ S.obj (𝟙_ C)))
    (q : F.obj M ⊗ S.obj (𝟙_ C) ⟶ S.obj (G.obj (F.obj M) ⊗ 𝟙_ C))
    (hp : ((adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)).app (S.obj (𝟙_ C))).app M = p)
    (hq : ((adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)).app (𝟙_ C)).app (F.obj M) = q)
    (ht : conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm = t) :
    (ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ p ≫
      R.map (q ≫ S.map (l.hom.app M ▷ (𝟙_ C) ≫ (ρ_ M).hom)) ≫
        t.hom.app M = 𝟙 M := by
  have hc := section_projection_unit adj adj' dF dG l M hl
  dsimp only at hc
  rw [hp, hq, ht] at hc
  exact hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem projection_flip_eq
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (A : C) (B : D) :
    (((adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)).app B).app A) =
      adj.homEquiv _ _ ((dF.app A).app (R.obj B) ≫
        (𝟙 (F.obj A) ⊗ₘ adj.counit.app B)) := by
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app,
    flipFunctor_map_app_app, curriedTensor_obj_map]
  rw [id_tensorHom]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_composite_id
    {C : Type*} [Category C] {A B C' D E : C}
    (a : A ≅ B) (b : B ≅ C') (p : C' ⟶ D) (q : D ⟶ E) (e : E ≅ A)
    [IsIso p] [IsIso q]
    (h : a.hom ≫ b.hom ≫ p ≫ q ≫ e.hom = 𝟙 A) :
    e.inv ≫ inv q ≫ inv p ≫ b.inv ≫ a.inv = 𝟙 A := by
  have hc : inv (a.hom ≫ b.hom ≫ p ≫ q ≫ e.hom) = inv (𝟙 A) :=
    IsIso.inv_eq_inv.mpr h
  simpa only [IsIso.inv_comp, IsIso.Iso.inv_hom, IsIso.inv_id, Category.assoc] using hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem section_inverse_id
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {S : C ⥤ D} (R : D ⥤ C) (t : S ⋙ R ≅ 𝟭 C) (M : C) (A : D)
    (p : M ⊗ R.obj (S.obj (𝟙_ C)) ⟶ R.obj A) (q : A ⟶ S.obj M)
    [hp : IsIso p] [hq : IsIso q]
    (hf : (ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ p ≫ R.map q ≫
      t.hom.app M = 𝟙 M) :
    t.inv.app M ≫ R.map (inv q) ≫ inv p ≫
      M ◁ t.hom.app (𝟙_ C) ≫ (ρ_ M).hom = 𝟙 M := by
  have hc := inverse_composite_id (ρ_ M).symm
    (whiskerLeftIso M (t.app (𝟙_ C)).symm) p (R.map q) (t.app M) hf
  simpa only [← Functor.map_inv, Iso.symm_hom, Iso.symm_inv,
    whiskerLeftIso_inv, Iso.app_hom, Iso.app_inv] using hc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.ProEtale

namespace ProjectionSection

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pullbackSection_def
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V : Scheme.{u}}
    (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    pullbackSection Λ r i h =
      (CondensedRing.leftDerivedUpperStarComp Λ i r).symm ≪≫
        Functor.leftDerivedFunctorNatIso (CondensedRing.upperStar Λ (i ≫ r))
          (eqToIso (congrArg (CondensedRing.upperStar Λ) h)) ≪≫
        CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X) ≪≫
        profinitePointModuleDerivedIdentity Λ X := rfl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [-instance] CategoryTheory.catToReflQuiver in
private local instance module_pull_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleDerivedPullback Λ f).Monoidal := by
  unfold moduleDerivedPullback
  exact CondensedRing.monoidal_leftDerivedUpperStar Λ f

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Both normalized equalities, with the inverse equality conditional on invertibility.
Source: blueprint clause (1), the two displayed normalization identities
(blueprint: lem-sfb-projection-section-normalization). -/
def Normalized {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  forward Λ r i h M = 𝟙 M ∧
    ∀ [IsIso (projection Λ r M
      ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
      [IsIso (sectionArrow Λ r i h M)], backward Λ r i h M = 𝟙 M

attribute [local irreducible] projection sectionArrow pullbackSection pushforwardSection
  forward backward

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem point_identity_eq (X : Scheme.{u}) :
    profinitePointModuleIdentity Λ X = CondensedRing.upperStarId Λ X := by
  have he : profinitePointModuleDirectImageIdentity Λ X = CondensedRing.lowerStarId Λ X := by
    exact (existsUnique_profinitePointModuleDirectImageIdentity Λ X).unique
      (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose_spec
      (fun M ↦ CondensedRing.lowerStarId_hom_app_hom Λ X M)
  simp only [profinitePointModuleIdentity, CondensedRing.upperStarId, he]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_identity_eq (X : Scheme.{u}) :
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X) ≪≫
      profinitePointModuleDerivedIdentity Λ X = CondensedRing.leftDerivedUpperStarId Λ X := by
  simp [profinitePointModuleDerivedIdentity, point_identity_eq,
    CondensedRing.leftDerivedUpperStarId, Functor.leftDerivedFunctorIdIso,
    Functor.leftDerivedFunctorNatIso, CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem derived_unit_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Functor.leftDerivedFunctorNatIso (CondensedRing.upperStar Λ f)
      (eqToIso (congrArg (CondensedRing.upperStar Λ) h))).hom.app (𝟙_ _) ≫
        (CondensedRing.leftDerivedUpperStarUnitIso Λ g).hom =
      (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom := by
  subst g
  simp only [eqToIso_refl, Functor.leftDerivedFunctorNatIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_refl,
    Category.id_comp, Iso.hom_inv_id_app]

attribute [local irreducible] CondensedRing.leftDerivedUpperStarComp
  CondensedRing.leftDerivedUpperStarId CondensedRing.leftDerivedUpperStarUnitIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory profinitePointModuleDerivedIdentity
  CondensedRing.leftDerivedUpperStarTensor
  Functor.leftDerivedFunctorNatIso Functor.leftDerivedFunctorIsoMapDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pullbackSection_unit {X V : Scheme.{u}}
    (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    (pullbackSection Λ r i h).hom.app (𝟙_ _) =
      (moduleDerivedPullback Λ i).map
        (CondensedRing.leftDerivedUpperStarUnitIso Λ r).hom ≫
          (CondensedRing.leftDerivedUpperStarUnitIso Λ i).hom := by
  have hid :
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X)).hom.app (𝟙_ _) ≫
        (profinitePointModuleDerivedIdentity Λ X).hom.app (𝟙_ _) =
      (CondensedRing.leftDerivedUpperStarId Λ X).hom.app (𝟙_ _) :=
    congrArg (fun e ↦ e.hom.app (𝟙_ _)) (derived_identity_eq Λ X)
  have hp := congrArg (fun e ↦ e.hom.app (𝟙_ _)) (pullbackSection_def Λ r i h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] at hp
  have ht := (congrArg (fun t ↦
      (Functor.leftDerivedFunctorNatIso (CondensedRing.upperStar Λ (i ≫ r))
        (eqToIso (congrArg (CondensedRing.upperStar Λ) h))).hom.app (𝟙_ _) ≫ t)
      (hid.trans (CondensedRing.leftDerivedUpperStarId_hom_app_unit Λ X))).trans
        (derived_unit_congr Λ h)
  have hc := CondensedRing.leftDerivedUpperStarComp_hom_app_unit Λ i r
  have hc' :
      ((CondensedRing.leftDerivedUpperStarComp Λ i r).app (𝟙_ _)).hom ≫
          (moduleDerivedPullback Λ i).map
            (CondensedRing.leftDerivedUpperStarUnitIso Λ r).hom ≫
            (CondensedRing.leftDerivedUpperStarUnitIso Λ i).hom =
        (CondensedRing.leftDerivedUpperStarUnitIso Λ (i ≫ r)).hom := by
    simpa only [Iso.app_hom, moduleDerivedPullback] using hc
  exact hp.trans ((congrArg (fun t ↦
    (CondensedRing.leftDerivedUpperStarComp Λ i r).inv.app (𝟙_ _) ≫ t)
      ht).trans ((Iso.inv_comp_eq
        ((CondensedRing.leftDerivedUpperStarComp Λ i r).app (𝟙_ _))).mpr
          (by simpa only [Category.assoc] using hc'.symm)))

attribute [-instance] CategoryTheory.catToReflQuiver in
private def moduleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleDerivedPullback Λ f ⊣ moduleDerivedPushforward Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

attribute [-instance] CategoryTheory.catToReflQuiver in
private def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (moduleDerivedPullback Λ f)).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj (moduleDerivedPullback Λ f)).obj
        (moduleDerivedPullback Λ f)).obj (curriedTensor _) :=
  postcomposeComparison (CondensedRing.upperStar Λ f).leftDerivedFunctor (curriedTensor _)
    (CondensedRing.leftDerivedUpperStarTensorRight Λ f)
    (CondensedRing.leftDerivedUpperStarTensor Λ f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem module_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.OplaxMonoidal.η (moduleDerivedPullback Λ f) =
      (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensorComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    Functor.OplaxMonoidal.δ (moduleDerivedPullback Λ f) A B =
      ((tensorComparison Λ f).app A).app B := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem module_projection_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (((moduleAdjunction Λ f).rightAdjointProjectionMap
      (T_C := (curriedTensor _).flip) (T_D := (curriedTensor _).flip)
      ((flipFunctor _ _ _).map (tensorComparison Λ f))).app B).app A =
        projection Λ f A B := by
  rw [projection_flip_eq]
  unfold projection moduleAdjunction tensorComparison
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem module_pushforwardSection_eq {X V : Scheme.{u}}
    (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    conjugateIsoEquiv ((moduleAdjunction Λ r).comp (moduleAdjunction Λ i))
      Adjunction.id (pullbackSection Λ r i h).symm = pushforwardSection Λ r i h := by
  unfold pushforwardSection moduleAdjunction
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem forward_eq_id {X V : Scheme.{u}}
    (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    forward Λ r i h M = 𝟙 M := by
  have ht := tensor_unit_comparison_compatibility
    (moduleDerivedPullback Λ r) (moduleDerivedPullback Λ i)
    (tensorComparison Λ r) (tensorComparison Λ i) (pullbackSection Λ r i h) M
    (by simpa only [module_unit Λ r, module_unit Λ i] using
      pullbackSection_unit Λ r i h)
    (tensorComparison_app Λ r M (𝟙_ _))
    (tensorComparison_app Λ i ((moduleDerivedPullback Λ r).obj M)
      ((moduleDerivedPullback Λ r).obj (𝟙_ _)))
  have hc := section_projection_unit_with_maps
    (C := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (D := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)))
    (F := moduleDerivedPullback Λ r) (R := moduleDerivedPushforward Λ r)
    (G := moduleDerivedPullback Λ i) (S := moduleDerivedPushforward Λ i)
    (moduleAdjunction Λ r) (moduleAdjunction Λ i)
    (tensorComparison Λ r) (tensorComparison Λ i) (pullbackSection Λ r i h) M ht
    (pushforwardSection Λ r i h)
    (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))
    (projection Λ i ((moduleDerivedPullback Λ r).obj M) (𝟙_ _))
    (module_projection_eq Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))
    (module_projection_eq Λ i ((moduleDerivedPullback Λ r).obj M) (𝟙_ _))
    (module_pushforwardSection_eq Λ r i h)
  unfold forward sectionArrow
  exact hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem backward_eq_id_of_forward {X V : Scheme.{u}}
    (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [hπ : IsIso (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
    [ha : IsIso (sectionArrow Λ r i h M)] (hf : forward Λ r i h M = 𝟙 M) :
    backward Λ r i h M = 𝟙 M := by
  have hc := section_inverse_id
    (C := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (D := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)))
    (S := moduleDerivedPushforward Λ i) (hp := hπ) (hq := ha)
    (moduleDerivedPushforward Λ r) (pushforwardSection Λ r i h) M
    (Arrow.mk (sectionArrow Λ r i h M)).left
    (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))
    (sectionArrow Λ r i h M) (by unfold forward at hf; exact hf)
  unfold backward
  exact hc

end ProjectionSection

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Projection normalization for a proper retraction and a closed section, on the
localizing closure of bounded constructible O_E-complexes. Source: blueprint
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1)
(blueprint: lem-sfb-projection-section-normalization).

Proof: transport the internal-module derived categories, K-flat relative tensors and
units to the section-ring sheaf categories by lem-pd-module-ringed-topos-derived-comparison.
That comparison identifies the actual derived pullback, pushforward, adjunction,
counit and tensor map, hence also their projection mates. The canonical direct-image
comparison of lem-weil-pbc-ringed-topoi-derived-pushforward-composition is the mate of
pullback composition, so agrees with pushforwardSection. Apply the final section clause
of lem-sfb-ringed-projection-tensor-composition with p = r, i the section and V = R_X.
Its symmetry convention gives exactly the two projections in forward. Under
pullbackSection and the right unitor the second projection is sectionArrow. Conjugating
the resulting identity of M tensor R_X by the right unitor gives the first equality.
When both displayed projections are inverted, invert this identity; functoriality
of Rr_* identifies the inverted middle factor with Rr_*(a_M inverse). This is backward.
-/
theorem projection_section_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (X V : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (r : V ⟶ X) (i : X ⟶ V) [IsProper r.left] [IsClosedImmersion i.left]
    (h : i.left ≫ r.left = 𝟙 X.left)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)))
    (_hM : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X.left) M) :
    ProjectionSection.Normalized (Profinite.padicIntegersRingObj ℓ E.1) r.left i.left h M := by
  have hf := ProjectionSection.forward_eq_id
    (Profinite.padicIntegersRingObj ℓ E.1) r.left i.left h M
  refine ⟨hf, ?_⟩
  intro hπ ha
  exact ProjectionSection.backward_eq_id_of_forward (hπ := hπ) (ha := ha)
    (Profinite.padicIntegersRingObj ℓ E.1) r.left i.left h M hf

end AlgebraicGeometry.ProEtale
