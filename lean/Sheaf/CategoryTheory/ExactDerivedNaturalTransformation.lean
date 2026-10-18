/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Natural transformations of exact functors on unbounded derived categories

Source: Stacks Project, Tag 04VG, localization universal property.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F F' F'' : C ⥤ D} [F.Additive] [F'.Additive] [F''.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits F''] [PreservesFiniteColimits F'']

/-- Descend a termwise natural transformation of exact functors through localization.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
noncomputable def mapDerivedCategoryNatTrans (τ : F ⟶ F') :
    F.mapDerivedCategory ⟶ F'.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (F'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory F'.mapDerivedCategory
    (Functor.whiskerRight (τ.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh)

/-- The value of the descended transformation on a homotopy representative.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
@[reassoc]
theorem mapDerivedCategoryNatTrans_fac (τ : F ⟶ F') (K : HomotopyCategory C (.up ℤ)) :
    (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Qh.obj K) ≫
        F'.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((τ.mapHomotopyCategory (.up ℤ)).app K) := by
  simp only [mapDerivedCategoryNatTrans, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  change F.mapDerivedCategoryFactorsh.hom.app K ≫
      DerivedCategory.Qh.map ((τ.mapHomotopyCategory (.up ℤ)).app K) ≫
      F'.mapDerivedCategoryFactorsh.inv.app K ≫
      F'.mapDerivedCategoryFactorsh.hom.app K = _
  simp only [Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

/-- Descent preserves composition.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_comp (τ : F ⟶ F') (υ : F' ⟶ F'') :
    mapDerivedCategoryNatTrans (τ ≫ υ) =
      mapDerivedCategoryNatTrans τ ≫ mapDerivedCategoryNatTrans υ := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [← cancel_mono (F''.mapDerivedCategoryFactorsh.hom.app K)]
  simp only [NatTrans.comp_app, Category.assoc, mapDerivedCategoryNatTrans_fac,
    mapDerivedCategoryNatTrans_fac_assoc, NatTrans.mapHomotopyCategory_comp,
    Functor.map_comp]

/-- On an isomorphism this is the existing exact-functor comparison.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_iso (e : F ≅ F') :
    mapDerivedCategoryNatTrans e.hom = (mapDerivedCategoryNatIso e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [← cancel_mono (F'.mapDerivedCategoryFactorsh.hom.app K),
    mapDerivedCategoryNatTrans_fac, mapDerivedCategoryNatIso_fach]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] in
private theorem mapHomotopyCategory_whiskerRight (τ : F ⟶ F') (G : D ⥤ E)
    [G.Additive] (K : HomotopyCategory C (.up ℤ)) :
    ((Functor.whiskerRight τ G).mapHomotopyCategory (.up ℤ)).app K =
      (G.mapHomotopyCategory (.up ℤ)).map ((τ.mapHomotopyCategory (.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] in
private theorem mapHomotopyCategory_whiskerLeft (G : E ⥤ C) [G.Additive]
    (τ : F ⟶ F') (K : HomotopyCategory E (.up ℤ)) :
    ((Functor.whiskerLeft G τ).mapHomotopyCategory (.up ℤ)).app K =
      (τ.mapHomotopyCategory (.up ℤ)).app ((G.mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rfl

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Descent commutes with postcomposition, through the canonical composition comparisons.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_whiskerRight (τ : F ⟶ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    mapDerivedCategoryNatTrans (Functor.whiskerRight τ G) ≫
        (mapDerivedCategoryCompIso F' G).hom =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatTrans τ) G.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (F'.mapDerivedCategoryFactorsh.hom.app K) ≫
    G.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factorsh, mapDerivedCategoryNatTrans_fac,
    ← G.mapDerivedCategory.map_comp_assoc, mapDerivedCategoryNatTrans_fac,
    G.mapDerivedCategory.map_comp_assoc]
  have hn := G.mapDerivedCategoryFactorsh.hom.naturality
    ((τ.mapHomotopyCategory (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [mapDerivedCategoryCompIso_hom_app_factorsh_assoc,
    mapHomotopyCategory_whiskerRight]

/-- Descent commutes with precomposition, through the canonical composition comparisons.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_whiskerLeft (G : E ⥤ C)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ F') :
    mapDerivedCategoryNatTrans (Functor.whiskerLeft G τ) ≫
        (mapDerivedCategoryCompIso G F').hom =
      (mapDerivedCategoryCompIso G F).hom ≫
        Functor.whiskerLeft G.mapDerivedCategory (mapDerivedCategoryNatTrans τ) := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso E (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (F'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
    F'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factorsh, mapDerivedCategoryNatTrans_fac,
    ← reassoc_of% ((mapDerivedCategoryNatTrans τ).naturality
      (G.mapDerivedCategoryFactorsh.hom.app K)), mapDerivedCategoryNatTrans_fac,
    mapDerivedCategoryCompIso_hom_app_factorsh_assoc, mapHomotopyCategory_whiskerLeft]

/-- Descent preserves identity transformations.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_id : mapDerivedCategoryNatTrans (𝟙 F) = 𝟙 _ := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K),
    mapDerivedCategoryNatTrans_fac]
  simp only [Functor.comp_obj, NatTrans.mapHomotopyCategory_id, NatTrans.id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- The postcomposition form with the target composition comparison inverted.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_whiskerRight_eq (τ : F ⟶ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    mapDerivedCategoryNatTrans (Functor.whiskerRight τ G) =
      (mapDerivedCategoryCompIso F G).hom ≫
        Functor.whiskerRight (mapDerivedCategoryNatTrans τ) G.mapDerivedCategory ≫
          (mapDerivedCategoryCompIso F' G).inv := by
  rw [← cancel_mono (mapDerivedCategoryCompIso F' G).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact mapDerivedCategoryNatTrans_whiskerRight τ G

/-- The precomposition form with the target composition comparison inverted.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_whiskerLeft_eq (G : E ⥤ C)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ F') :
    mapDerivedCategoryNatTrans (Functor.whiskerLeft G τ) =
      (mapDerivedCategoryCompIso G F).hom ≫
        Functor.whiskerLeft G.mapDerivedCategory (mapDerivedCategoryNatTrans τ) ≫
          (mapDerivedCategoryCompIso G F').inv := by
  rw [← cancel_mono (mapDerivedCategoryCompIso G F').hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact mapDerivedCategoryNatTrans_whiskerLeft G τ

private theorem comp_middle
    {B₀ B₁ B₂ B₃ : Type*} [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    [Abelian B₀] [Abelian B₁] [Abelian B₂] [Abelian B₃]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁]
    [HasDerivedCategory B₂] [HasDerivedCategory B₃]
    (F : B₀ ⥤ B₁) (G : B₁ ⥤ B₂) (H : B₂ ⥤ B₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : DerivedCategory B₀) :
    (mapDerivedCategoryCompIso (F ⋙ G) H).inv.app K ≫
        (mapDerivedCategoryCompIso F (G ⋙ H)).hom.app K =
      H.mapDerivedCategory.map ((mapDerivedCategoryCompIso F G).hom.app K) ≫
        (mapDerivedCategoryCompIso G H).inv.app (F.mapDerivedCategory.obj K) := by
  have hc := congr_app (mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [← cancel_epi ((mapDerivedCategoryCompIso (F ⋙ G) H).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hc, Iso.hom_inv_id_app, Category.comp_id]

private theorem comp_middle_inv
    {B₀ B₁ B₂ B₃ : Type*} [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    [Abelian B₀] [Abelian B₁] [Abelian B₂] [Abelian B₃]
    [HasDerivedCategory B₀] [HasDerivedCategory B₁]
    [HasDerivedCategory B₂] [HasDerivedCategory B₃]
    (F : B₀ ⥤ B₁) (G : B₁ ⥤ B₂) (H : B₂ ⥤ B₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : DerivedCategory B₀) :
    (mapDerivedCategoryCompIso F (G ⋙ H)).inv.app K ≫
        (mapDerivedCategoryCompIso (F ⋙ G) H).hom.app K =
      (mapDerivedCategoryCompIso G H).hom.app (F.mapDerivedCategory.obj K) ≫
        H.mapDerivedCategory.map ((mapDerivedCategoryCompIso F G).inv.app K) := by
  have hc := congr_app (mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [← cancel_epi ((mapDerivedCategoryCompIso F (G ⋙ H)).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hc, ← H.mapDerivedCategory.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Category.comp_id]

section ProjectionSquare

variable {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄] [Abelian C₅]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄] [HasDerivedCategory C₅]
  (E : C₀ ⥤ C₁) (P : C₁ ⥤ C₂) (J : C₀ ⥤ C₂)
  (H : C₀ ⥤ C₃) (E' : C₃ ⥤ C₄) (P' : C₄ ⥤ C₅) (J' : C₃ ⥤ C₅)
  (G : C₁ ⥤ C₄) (T : C₂ ⥤ C₅)
  [E.Additive] [P.Additive] [J.Additive] [H.Additive] [E'.Additive]
  [P'.Additive] [J'.Additive] [G.Additive] [T.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- A commutative square between triangular transformations remains commutative after
passing to unbounded derived categories.
Source: Stacks Project, Tag 04VG.
(blueprint: lem-a2-exact-derived-natural-transformations). -/
theorem mapDerivedCategoryNatTrans_projectionSquare
    (σ : E ⋙ G ≅ H ⋙ E') (θ : G ⋙ P' ≅ P ⋙ T) (j : H ⋙ J' ≅ J ⋙ T)
    (δ : E ⋙ P ⟶ J) (δ' : E' ⋙ P' ⟶ J')
    (hδ : Functor.whiskerRight σ.hom P' ≫ (Functor.associator H E' P').hom ≫
        Functor.whiskerLeft H δ' ≫ j.hom =
      (Functor.associator E G P').hom ≫ Functor.whiskerLeft E θ.hom ≫
        (Functor.associator E P T).inv ≫ Functor.whiskerRight δ T)
    (K : DerivedCategory C₀) :
    P'.mapDerivedCategory.map ((mapDerivedCategorySquareIso σ).hom.app K) ≫
        (mapDerivedCategoryCompIso E' P').inv.app (H.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryNatTrans δ').app (H.mapDerivedCategory.obj K) ≫
        (mapDerivedCategorySquareIso j).hom.app K =
      (mapDerivedCategorySquareIso θ).hom.app (E.mapDerivedCategory.obj K) ≫
        T.mapDerivedCategory.map ((mapDerivedCategoryCompIso E P).inv.app K ≫
          (mapDerivedCategoryNatTrans δ).app K) := by
  have h := congrArg (fun τ ↦ (mapDerivedCategoryNatTrans τ).app K) hδ
  have ha : mapDerivedCategoryNatTrans (Functor.associator H E' P').hom = 𝟙 _ :=
    mapDerivedCategoryNatTrans_id
  have hb : mapDerivedCategoryNatTrans (Functor.associator E G P').hom = 𝟙 _ :=
    mapDerivedCategoryNatTrans_id
  have hc : mapDerivedCategoryNatTrans (Functor.associator E P T).inv = 𝟙 _ :=
    mapDerivedCategoryNatTrans_id
  simp only [mapDerivedCategoryNatTrans_comp, mapDerivedCategoryNatTrans_whiskerRight_eq,
    mapDerivedCategoryNatTrans_whiskerLeft_eq, mapDerivedCategoryNatTrans_iso,
    ha, hb, hc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc, Category.id_comp] at h
  rw [reassoc_of% (comp_middle H E' P' K),
    reassoc_of% (comp_middle_inv E P T K)] at h
  rw [← cancel_epi ((mapDerivedCategoryCompIso (E ⋙ G) P').hom.app K ≫
      P'.mapDerivedCategory.map ((mapDerivedCategoryCompIso E G).hom.app K)),
    ← cancel_mono ((mapDerivedCategoryCompIso J T).inv.app K)]
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  have he := congr_app (mapDerivedCategoryCompIso_assoc E G P') K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at he
  rw [← reassoc_of% he, Iso.hom_inv_id_app_assoc]
  simpa only [Functor.map_comp, Category.assoc, Category.comp_id] using h

end ProjectionSquare

end CategoryTheory.Functor
