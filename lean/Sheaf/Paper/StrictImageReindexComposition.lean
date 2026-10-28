/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3 -/
module

public import Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude
import Sheaf.CategoryTheory.DerivedExactSquareCoherence
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.RightDerivedExactRestrictionNormalization

/-! # Composition of arithmetic selection through the strict image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem move_inverse_compositors
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X₀ X₁ : A} {Y₀ Y₁ : B} (a : X₀ ≅ X₁) (b : Y₀ ≅ Y₁)
    (f : F.obj X₀ ⟶ Y₀) (g : F.obj X₁ ⟶ Y₁)
    (hf : F.map a.inv ≫ f = g ≫ b.inv) : F.map a.hom ≫ g = f ≫ b.hom := by
  have hd := congrArg (fun z ↦ F.map a.hom ≫ z ≫ b.hom) hf
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
    Iso.inv_hom_id, F.map_id, Category.id_comp, Category.comp_id] at hd
  exact hd.symm


private theorem invert_selection_composition
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    (e h p : A ⥤ A) (e' h' p' : B ⥤ B)
    (rE : F ⋙ e' ≅ e ⋙ F) (rH : F ⋙ h' ≅ h ⋙ F)
    (rP : F ⋙ p' ≅ p ⋙ F) (q : h ⋙ e ≅ p) (q' : h' ⋙ e' ≅ p')
    (hc : ∀ K, e'.map (rH.hom.app K) ≫ rE.hom.app (h.obj K) ≫
      F.map (q.hom.app K) = q'.hom.app (F.obj K) ≫ rP.hom.app K) (K : A) :
    F.map (q.hom.app K) ≫ rP.inv.app K =
      rE.inv.app (h.obj K) ≫ e'.map (rH.inv.app K) ≫ q'.hom.app (F.obj K) := by
  have hd := congrArg (fun z ↦ rE.inv.app (h.obj K) ≫
    e'.map (rH.inv.app K) ≫ z ≫ rP.inv.app K) (hc K)
  simp only [Category.assoc, ← e'.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at hd
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] at hd
  exact hd


private theorem paste_selection_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C)
    (e h p : A ⥤ A) (e' h' p' : B ⥤ B) (e'' h'' p'' : C ⥤ C)
    (rE : e ⋙ F ≅ F ⋙ e') (rH : h ⋙ F ≅ F ⋙ h')
    (rP : p ⋙ F ≅ F ⋙ p')
    (sE : e' ⋙ G ≅ G ⋙ e'') (sH : h' ⋙ G ≅ G ⋙ h'')
    (sP : p' ⋙ G ≅ G ⋙ p'')
    (q : h ⋙ e ≅ p) (q' : h' ⋙ e' ≅ p') (q'' : h'' ⋙ e'' ≅ p'')
    (hr : ∀ K, F.map (q.hom.app K) ≫ rP.hom.app K =
      rE.hom.app (h.obj K) ≫ e'.map (rH.hom.app K) ≫ q'.hom.app (F.obj K))
    (hs : ∀ K, G.map (q'.hom.app K) ≫ sP.hom.app K =
      sE.hom.app (h'.obj K) ≫ e''.map (sH.hom.app K) ≫ q''.hom.app (G.obj K))
    (K : A) :
    G.map (F.map (q.hom.app K)) ≫ G.map (rP.hom.app K) ≫ sP.hom.app (F.obj K) =
      G.map (rE.hom.app (h.obj K)) ≫ sE.hom.app (F.obj (h.obj K)) ≫
        e''.map (G.map (rH.hom.app K)) ≫ e''.map (sH.hom.app (F.obj K)) ≫
        q''.hom.app (G.obj (F.obj K)) := by
  rw [← G.map_comp_assoc, hr]
  simp only [G.map_comp, Category.assoc]
  rw [hs]
  have hn := sE.hom.naturality (rH.hom.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]


private theorem normalized_reindex_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (v + 1)}
    [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
    [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{w} A₀] [HasDerivedCategory.{w} A₁]
    [HasDerivedCategory.{w} A₂] [HasDerivedCategory.{w} B₀]
    [HasDerivedCategory.{w} B₁] [HasDerivedCategory.{w} B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions A₂]
    (H₀ : A₀ ⥤ B₀) (H₁ : A₁ ⥤ B₁) (H₂ : A₂ ⥤ B₂)
    (x₀ : A₀ ⥤ A₁) (x₁ : A₁ ⥤ A₂) (x₂ : A₀ ⥤ A₂)
    (y₀ : B₀ ⥤ B₁) (y₁ : B₁ ⥤ B₂) (y₂ : B₀ ⥤ B₂)
    [H₀.Additive] [H₁.Additive] [H₂.Additive]
    [x₀.Additive] [x₁.Additive] [x₂.Additive]
    [y₀.Additive] [y₁.Additive] [y₂.Additive]
    [PreservesFiniteLimits x₀] [PreservesFiniteColimits x₀]
    [PreservesFiniteLimits x₁] [PreservesFiniteColimits x₁]
    [PreservesFiniteLimits x₂] [PreservesFiniteColimits x₂]
    [PreservesFiniteLimits y₀] [PreservesFiniteColimits y₀]
    [PreservesFiniteLimits y₁] [PreservesFiniteColimits y₁]
    [PreservesFiniteLimits y₂] [PreservesFiniteColimits y₂]
    (c₀ : H₀ ⋙ y₀ ≅ x₀ ⋙ H₁) (c₁ : H₁ ⋙ y₁ ≅ x₁ ⋙ H₂)
    (c₂ : H₀ ⋙ y₂ ≅ x₂ ⋙ H₂)
    (δ₀ : H₀.rightDerivedFunctor ⋙ y₀.mapDerivedCategory ≅
      x₀.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (δ₁ : H₁.rightDerivedFunctor ⋙ y₁.mapDerivedCategory ≅
      x₁.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (δ₂ : H₀.rightDerivedFunctor ⋙ y₂.mapDerivedCategory ≅
      x₂.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (ρZ : x₀ ⋙ x₁ ≅ x₂) (ρW : y₀ ⋙ y₁ ≅ y₂)
    (hn₀ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₁ x₀ y₀
      x₀.mapDerivedCategory y₀.mapDerivedCategory
      x₀.mapDerivedCategoryFactors y₀.mapDerivedCategoryFactors c₀.hom δ₀.hom)
    (hn₁ : CategoryTheory.ExactDerivedSquare.unitNormalized H₁ H₂ x₁ y₁
      x₁.mapDerivedCategory y₁.mapDerivedCategory
      x₁.mapDerivedCategoryFactors y₁.mapDerivedCategoryFactors c₁.hom δ₁.hom)
    (hn₂ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₂ x₂ y₂
      x₂.mapDerivedCategory y₂.mapDerivedCategory
      x₂.mapDerivedCategoryFactors y₂.mapDerivedCategoryFactors c₂.hom δ₂.hom)
    (hc : ∀ N : A₀, ρW.hom.app (H₀.obj N) ≫ c₂.hom.app N =
      y₁.map (c₀.hom.app N) ≫ c₁.hom.app (x₀.obj N) ≫ H₂.map (ρZ.hom.app N))
    (K : DerivedCategory.{w} A₀) :
    y₁.mapDerivedCategory.map (δ₀.hom.app K) ≫
        δ₁.hom.app (x₀.mapDerivedCategory.obj K) ≫
        H₂.rightDerivedFunctor.map
          ((Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom.app K) =
      (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom.app
          (H₀.rightDerivedFunctor.obj K) ≫ δ₂.hom.app K := by
  have hnorm : CategoryTheory.ExactDerivedSquare.unitNormalized
      H₀ H₂ (x₀ ⋙ x₁) (y₀ ⋙ y₁)
      (x₀.mapDerivedCategory ⋙ x₁.mapDerivedCategory)
      (y₀.mapDerivedCategory ⋙ y₁.mapDerivedCategory)
      (Functor.isoWhiskerRight x₀.mapDerivedCategoryFactors x₁.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (x₀.mapHomologicalComplex (.up ℤ)) x₁.mapDerivedCategoryFactors)
      (Functor.isoWhiskerRight y₀.mapDerivedCategoryFactors y₁.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (y₀.mapHomologicalComplex (.up ℤ)) y₁.mapDerivedCategoryFactors)
      (Functor.whiskerRight c₀.hom y₁ ≫ Functor.whiskerLeft x₀ c₁.hom)
      (Functor.whiskerRight δ₀.hom y₁.mapDerivedCategory ≫
        Functor.whiskerLeft x₀.mapDerivedCategory δ₁.hom) := by
    intro I
    simp only [Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Category.assoc, Functor.map_comp]
    erw [← reassoc_of% δ₁.hom.naturality (x₀.mapDerivedCategoryFactors.hom.app I)]
    simp only [Functor.comp_obj]
    erw [← y₁.mapDerivedCategory.map_comp_assoc, ← y₁.mapDerivedCategory.map_comp_assoc]
    erw [Category.assoc, hn₀ I]
    simp only [Functor.map_comp, Category.assoc]
    erw [hn₁ ((x₀.mapHomologicalComplex (.up ℤ)).obj I)]
    erw [reassoc_of% (y₁.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex c₀.hom (.up ℤ)).app I))]
    simp only [← DerivedCategory.Q.map_comp_assoc]
    rfl
  have h := CategoryTheory.ExactDerivedSquare.normalized_naturality
    H₀ H₂ (x₀ ⋙ x₁) (y₀ ⋙ y₁) x₂ y₂
    (x₀.mapDerivedCategory ⋙ x₁.mapDerivedCategory) x₂.mapDerivedCategory
    (y₀.mapDerivedCategory ⋙ y₁.mapDerivedCategory) y₂.mapDerivedCategory
    (Functor.isoWhiskerRight x₀.mapDerivedCategoryFactors x₁.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (x₀.mapHomologicalComplex (.up ℤ)) x₁.mapDerivedCategoryFactors)
    x₂.mapDerivedCategoryFactors
    (Functor.isoWhiskerRight y₀.mapDerivedCategoryFactors y₁.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (y₀.mapHomologicalComplex (.up ℤ)) y₁.mapDerivedCategoryFactors)
    y₂.mapDerivedCategoryFactors
    (Functor.whiskerRight c₀.hom y₁ ≫ Functor.whiskerLeft x₀ c₁.hom) c₂.hom
    (Functor.whiskerRight δ₀.hom y₁.mapDerivedCategory ≫
      Functor.whiskerLeft x₀.mapDerivedCategory δ₁.hom) δ₂.hom
    hnorm hn₂ ρZ.hom ρW.hom
    (Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom
    (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom
    (fun P ↦ by
      simpa only [Functor.exactDerivedRestrictionComposition,
        Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatIso.mapHomologicalComplex, Category.assoc]
        using Functor.exactDerivedRestrictionComposition_hom_factors x₀ x₁ x₂ ρZ P)
    (fun P ↦ by
      simpa only [Functor.exactDerivedRestrictionComposition,
        Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatIso.mapHomologicalComplex, Category.assoc]
        using Functor.exactDerivedRestrictionComposition_hom_factors y₀ y₁ y₂ ρW P)
    (fun N ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using hc N)
  have hh := NatTrans.congr_app h K
  change (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom.app
        (H₀.rightDerivedFunctor.obj K) ≫ δ₂.hom.app K =
    (y₁.mapDerivedCategory.map (δ₀.hom.app K) ≫
      δ₁.hom.app (x₀.mapDerivedCategory.obj K)) ≫
      H₂.rightDerivedFunctor.map
        ((Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom.app K) at hh
  rw [Category.assoc] at hh
  exact hh.symm

section ExactSquares

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits (F₀₁ ⋙ F₁₂)] [PreservesFiniteColimits (F₀₁ ⋙ F₁₂)]
  [PreservesFiniteLimits (G₀₁ ⋙ G₁₂)] [PreservesFiniteColimits (G₀₁ ⋙ G₁₂)]

private theorem localized_square_comp
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ X : C₀,
      U₂.map (cF.hom.app X) ≫ q₁₂.hom.app (F₀₁.obj X) ≫
        G₁₂.map (q₀₁.hom.app X) = q₀₂.hom.app X ≫ cG.hom.app (U₀.obj X))
    (K : DerivedCategory C₀) :
    U₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso cF ≪≫
          Functor.mapDerivedCategoryCompIso F₀₁ F₁₂).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso q₁₂).hom.app (F₀₁.mapDerivedCategory.obj K) ≫
      G₁₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q₀₁).hom.app K) =
    (Functor.mapDerivedCategorySquareIso q₀₂).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso cG ≪≫ Functor.mapDerivedCategoryCompIso G₀₁ G₁₂).hom.app
        (U₀.mapDerivedCategory.obj K) := by
  have hi := Functor.mapDerivedCategorySquareIso_comp
    F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂ q₀₁ q₁₂ q₀₂ cF cG hq
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using
    NatTrans.congr_app (congrArg (fun z ↦ z.hom) hi) K

end ExactSquares

private theorem localized_square_symm_hom
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso q.symm).hom =
      (Functor.mapDerivedCategorySquareIso q).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem normalize_presented_square
    {A B C D : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (W : B ⥤ D)
    [F.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [V.PreservesKInjectiveComplexes] (a : F ⋙ W ≅ V ⋙ G)
    (b : F.rightDerivedFunctor ⋙ W.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : b = (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F W).symm ≪≫
      Functor.rightDerivedFunctorNatIso a ≪≫ Functor.rightDerivedFunctorCompIso V G ≪≫
        Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor) :
    CategoryTheory.ExactDerivedSquare.unitNormalized F G V W
      V.mapDerivedCategory W.mapDerivedCategory
      V.mapDerivedCategoryFactors W.mapDerivedCategoryFactors a.hom b.hom := by
  subst b
  exact CategoryTheory.rightDerivedExactRestriction_normalization F G V W a

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem reindexProper_normalized {X Y : Scheme.{u}} (g : X ⟶ Y)
    (e : ℕ) (he : 1 ≤ e) :
    CategoryTheory.ExactDerivedSquare.unitNormalized
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
      (ordinarySubsequence l E X e) (ordinarySubsequence l E Y e)
      (subsequence l E X e) (subsequence l E Y e)
      (ordinarySubsequence l E X e).mapDerivedCategoryFactors
      (ordinarySubsequence l E Y e).mapDerivedCategoryFactors
      (reindexProperOrdinary l E g e).hom (reindexProper l E g e he).hom := by
  have := subsequence_preservesKInjective l E X e he
  apply normalize_presented_square
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (ordinarySubsequence l E X e) (ordinarySubsequence l E Y e)
    (reindexProperOrdinary l E g e) (reindexProper l E g e he)
  rfl


private theorem reindexProper_composition {X Y : Scheme.{u}} (g : X ⟶ Y)
    (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
        ((compositionRetained l E X e h he hh).hom.app K) ≫
        (reindexProper l E g (h * e) (one_le_mul hh he)).inv.app K =
      (reindexProper l E g e he).inv.app ((subsequence l E X h).obj K) ≫
        (subsequence l E Y e).map ((reindexProper l E g h hh).inv.app K) ≫
        (compositionRetained l E Y e h he hh).hom.app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) := by
  apply invert_selection_composition
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (subsequence l E X e) (subsequence l E X h) (subsequence l E X (h * e))
    (subsequence l E Y e) (subsequence l E Y h) (subsequence l E Y (h * e))
    (reindexProper l E g e he) (reindexProper l E g h hh)
    (reindexProper l E g (h * e) (one_le_mul hh he))
    (compositionRetained l E X e h he hh) (compositionRetained l E Y e h he hh)
  intro N
  apply normalized_reindex_composition
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (ordinarySubsequence l E X h) (ordinarySubsequence l E X e)
    (ordinarySubsequence l E X (h * e))
    (ordinarySubsequence l E Y h) (ordinarySubsequence l E Y e)
    (ordinarySubsequence l E Y (h * e))
    (reindexProperOrdinary l E g h) (reindexProperOrdinary l E g e)
    (reindexProperOrdinary l E g (h * e))
    (reindexProper l E g h hh) (reindexProper l E g e he)
    (reindexProper l E g (h * e) (one_le_mul hh he))
    (eqToIso (compositionSelectionOrdinary l E X e h he hh))
    (eqToIso (compositionSelectionOrdinary l E Y e h he hh))
    (reindexProper_normalized l E g h hh) (reindexProper_normalized l E g e he)
    (reindexProper_normalized l E g (h * e) (one_le_mul hh he))
    ?_ N
  intro M
  simp only [reindexProperOrdinary, Iso.refl_hom, NatTrans.id_app,
    eqToIso.hom, eqToHom_app, eqToHom_map]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


private theorem reindexOpen_composition {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
        ((compositionRetained l E X e h he hh).hom.app K) ≫
        (reindexOpen l E g (h * e)).inv.app K =
      (reindexOpen l E g e).inv.app ((subsequence l E X h).obj K) ≫
        (subsequence l E Y e).map ((reindexOpen l E g h).inv.app K) ≫
        (compositionRetained l E Y e h he hh).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) := by
  have hf := localized_square_comp
    (ordinarySubsequence l E X h) (ordinarySubsequence l E X e)
    (ordinarySubsequence l E X (h * e))
    (ordinarySubsequence l E Y h) (ordinarySubsequence l E Y e)
    (ordinarySubsequence l E Y (h * e))
    (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (reindexOpenOrdinary l E g h).symm (reindexOpenOrdinary l E g e).symm
    (reindexOpenOrdinary l E g (h * e)).symm
    (eqToIso (compositionSelectionOrdinary l E X e h he hh)).symm
    (eqToIso (compositionSelectionOrdinary l E Y e h he hh)).symm
    (fun M ↦ by
      simp only [reindexOpenOrdinary, Iso.symm_hom, Iso.refl_inv,
        NatTrans.id_app, eqToIso.inv, eqToHom_app, eqToHom_map]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]) K
  simp only [localized_square_symm_hom] at hf
  have hcomp (W : Scheme.{u}) :
      (Functor.mapDerivedCategoryNatIso
          (eqToIso (compositionSelectionOrdinary l E W e h he hh)).symm ≪≫
        Functor.mapDerivedCategoryCompIso
          (ordinarySubsequence l E W h) (ordinarySubsequence l E W e)).hom =
      (compositionRetained l E W e h he hh).inv := by
    simp only [Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom,
      compositionRetained, Iso.trans_inv, Iso.symm_inv]
  simp only [hcomp] at hf
  have hf' :
      (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((compositionRetained l E X e h he hh).inv.app K) ≫
        (reindexOpen l E g e).inv.app ((subsequence l E X h).obj K) ≫
        (subsequence l E Y e).map ((reindexOpen l E g h).inv.app K) =
      (reindexOpen l E g (h * e)).inv.app K ≫
        (compositionRetained l E Y e h he hh).inv.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) := hf
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using move_inverse_compositors
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    ((compositionRetained l E X e h he hh).app K)
    ((compositionRetained l E Y e h he hh).app
      ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K))
    ((reindexOpen l E g e).inv.app ((subsequence l E X h).obj K) ≫
      (subsequence l E Y e).map ((reindexOpen l E g h).inv.app K))
    ((reindexOpen l E g (h * e)).inv.app K) hf'


/-- Nested selections through a proper/open image agree with the composite selection.
Source: Stacks 0D6E, 0E8I, 0940; support realization, image-selection step.
(blueprint: lem-pur-strict-image-reindex-composition).
Proof: the ordinary proper and open selection squares are identity squares.
Pasting the squares for indices e and h gives the square for h*e, after
`compositionSelectionOrdinary` identifies the retained levels and transitions.
The canonical derived-composite comparisons preserve this pasting: their
whole-complex unit equations give identical composites with the derived unit,
and right-derived uniqueness proves equality. Positive selection preserves
K-injectives, so these comparisons are isomorphisms. Paste proper and exact open
comparisons in the order defining reindexImage, and invert the selection squares.
The exact derived-composition comparison is precisely compositionRetained. -/
theorem reindexImage_composition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (image l E c).map ((compositionRetained l E X e h he hh).hom.app K) ≫
        (reindexImage l E c (h * e) (one_le_mul hh he)).inv.app K =
      (reindexImage l E c e he).inv.app ((subsequence l E X h).obj K) ≫
        (subsequence l E Y e).map ((reindexImage l E c h hh).inv.app K) ≫
        (compositionRetained l E Y e h he hh).hom.app ((image l E c).obj K) := by
  have hp := paste_selection_composition
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i)
    (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g)
    (subsequence l E X e) (subsequence l E X h) (subsequence l E X (h * e))
    (subsequence l E c.Z e) (subsequence l E c.Z h)
    (subsequence l E c.Z (h * e))
    (subsequence l E Y e) (subsequence l E Y h) (subsequence l E Y (h * e))
    (reindexOpen l E c.i e).symm (reindexOpen l E c.i h).symm
    (reindexOpen l E c.i (h * e)).symm
    (reindexProper l E c.g e he).symm (reindexProper l E c.g h hh).symm
    (reindexProper l E c.g (h * e) (one_le_mul hh he)).symm
    (compositionRetained l E X e h he hh)
    (compositionRetained l E c.Z e h he hh)
    (compositionRetained l E Y e h he hh)
    (reindexOpen_composition l E c.i e h he hh)
    (reindexProper_composition l E c.g e h he hh) K
  simpa only [reindexImage, image, Iso.trans_inv, Iso.symm_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using hp

end WeilConjectures.PurStrictScalar
