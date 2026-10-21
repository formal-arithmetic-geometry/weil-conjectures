/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-!
# Naturality of normalized scalar reduction boundaries

The quotient and Kummer identifications are characterized by adjunction units.
Their naturality, and the naturality of the resulting degree-two boundary, are formal
consequences of the exact right-adjoint square and its shift-compatible derived mate.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _

private theorem single_factors (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) := by
  erw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
  erw [Iso.hom_inv_id_app_assoc]

private theorem square_single (e : F ⋙ G ≅ H ⋙ I) (X : A) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj X
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cH := HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0
  let cI := HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hc : ec.hom.app K ≫ (I.mapHomologicalComplex (.up ℤ)).map (cH.hom.app X) ≫
      cI.hom.app (H.obj X) =
      (G.mapHomologicalComplex (.up ℤ)).map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X) := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        ec, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.single_map_f_self, cF, cG, cH, cI,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
      simpa only [K, CategoryTheory.Functor.comp_map, Category.assoc] using!
        congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((H ⋙ I).obj X)).inv)
          (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).symm
    · exact ((F ⋙ G).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi)).eq_of_src _ _
  rw [single_factors H X, single_factors I (H.obj X), single_factors F X,
    single_factors G (F.obj X)]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [I.mapDerivedCategoryFactors.hom.naturality_assoc (cH.hom.app X)]
  erw [reassoc_of% (square_factors F G H I e K)]
  erw [G.mapDerivedCategoryFactors.hom.naturality_assoc (cF.hom.app X)]
  congr 2
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  simp only [← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q.congr_map hc
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [R'.CommShift ℤ]
  (ρ : R ⋙ F ≅ G ⋙ R') [NatTrans.CommShift ρ.hom ℤ]
private theorem shifted_square (Y : B) (s : ℤ) :
    F.map ((R.commShiftIso s).inv.app Y) ≫ ρ.hom.app (Y⟦s⟧) ≫
      R'.map ((G.commShiftIso s).hom.app Y) ≫ (R'.commShiftIso s).hom.app (G.obj Y) =
    (F.commShiftIso s).hom.app (R.obj Y) ≫ (ρ.hom.app Y)⟦s⟧' := by
  have h := ρ.hom.shift_app_comm s Y
  simp only [Functor.commShiftIso_comp_hom_app] at h
  apply (cancel_epi (F.map ((R.commShiftIso s).hom.app Y))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using h.symm
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

private theorem shifted_single_square (Y : B) (s : ℤ) :
    F.mapDerivedCategory.map
        (((R.mapDerivedCategorySingleFunctor 0).inv.app Y)⟦s⟧' ≫
          (R.mapDerivedCategory.commShiftIso s).inv.app
            ((DerivedCategory.singleFunctor B 0).obj Y)) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj Y)⟦s⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso s).hom.app
            ((DerivedCategory.singleFunctor B 0).obj Y) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦s⟧') ≫
      (R'.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj (G.obj Y)) ≫
      ((R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y))⟦s⟧' =
    (F.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj (R.obj Y)) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y))⟦s⟧' := by
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  have : NatTrans.CommShift ρd.hom ℤ := by
    dsimp only [ρd, CategoryTheory.Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h : F.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
      ρd.hom.app ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      R'.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
      (R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y) := by
    erw [square_single R F G R' ρ Y]
    rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      F.mapDerivedCategory.map_id]
    erw [Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [R'.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) s]
  erw [reassoc_of% (shifted_square R.mapDerivedCategory F.mapDerivedCategory
    G.mapDerivedCategory R'.mapDerivedCategory ρd
      ((DerivedCategory.singleFunctor B 0).obj Y) s)]
  erw [F.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) s]
  simp only [← (shiftFunctor (DerivedCategory A') s).map_comp]
  rw [h]
  rfl
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')


private noncomputable def restrictionBoundary (n : ℕ) (X : A) (Y : B) (i : R.obj Y ⟶ X)
    (hz : i ≫ (n • 𝟙 X) = 0)
    (hS : (ShortComplex.mk i (n • 𝟙 X) hz).ShortExact) :
    (DerivedCategory.singleFunctor A 0).obj X ⟶
      R.mapDerivedCategory.obj (((DerivedCategory.singleFunctor B 0).obj Y)⟦(1 : ℤ)⟧) :=
  hS.singleδ ≫ ((R.mapDerivedCategorySingleFunctor 0).inv.app Y)⟦(1 : ℤ)⟧' ≫
    (R.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.singleFunctor B 0).obj Y)
private theorem kummer_square
    (n : ℕ) (X : A) (X' : A') (Y : B) (Y' : B')
    (i : R.obj Y ⟶ X) (i' : R'.obj Y' ⟶ X')
    (hz : i ≫ (n • 𝟙 X) = 0) (hz' : i' ≫ (n • 𝟙 X') = 0)
    (hS : (ShortComplex.mk i (n • 𝟙 X) hz).ShortExact)
    (hS' : (ShortComplex.mk i' (n • 𝟙 X') hz').ShortExact)
    (f : X' ≅ F.obj X) (h : Y' ≅ G.obj Y)
    (hi : i' ≫ f.hom = R'.map h.hom ≫ ρ.inv.app Y ≫ F.map i) :
    F.mapDerivedCategory.map (restrictionBoundary R n X Y i hz hS) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj Y)⟦(1 : ℤ)⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor B 0).obj Y) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(1 : ℤ)⟧') =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor A' 0).map f.inv ≫
      restrictionBoundary R' n X' Y' i' hz' hS' ≫
      R'.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor B' 0).map h.hom)⟦(1 : ℤ)⟧') := by
  let S := ShortComplex.mk i (n • 𝟙 X) hz
  let S' := ShortComplex.mk i' (n • 𝟙 X') hz'
  let j := ρ.hom.app Y ≫ R'.map h.inv
  have hji : F.map i ≫ f.inv = j ≫ i' := by
    apply (cancel_mono f.hom).1
    dsimp only [j]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hi]
    simp only [← R'.map_comp_assoc, Iso.inv_hom_id, R'.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc]
  let k : F.mapShortComplex.obj S ⟶ S' :=
    ShortComplex.homMk j f.inv f.inv hji.symm (by
      change f.inv ≫ (n • 𝟙 X') = F.map (n • 𝟙 X) ≫ f.inv
      simp)
  have hk := (ShortComplex.ShortExact.singleTriangle.map (hS.map_of_exact F) hS' k).comm₃
  have hδ :
      F.mapDerivedCategory.map hS.singleδ ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj (R.obj Y)) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y))⟦(1 : ℤ)⟧' =
      (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫ (hS.map_of_exact F).singleδ := by
    have hh := hS.mapShiftedHom_singleδ' F
    apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app X)).1
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, ShiftedHom.map] using hh
  apply (cancel_mono
    ((R'.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj (G.obj Y)) ≫
      ((R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y))⟦(1 : ℤ)⟧')).1
  dsimp only [restrictionBoundary]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hs := shifted_single_square R F G R' ρ Y (1 : ℤ)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hs
  erw [hs]
  rw [reassoc_of% hδ]
  erw [R'.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((DerivedCategory.singleFunctor B' 0).map h.hom) (1 : ℤ)]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← (shiftFunctor (DerivedCategory A') (1 : ℤ)).map_comp]
  erw [(R'.mapDerivedCategorySingleFunctor 0).hom.naturality h.hom]
  erw [← (shiftFunctor (DerivedCategory A') (1 : ℤ)).map_comp,
    Iso.inv_hom_id_app_assoc]
  change _ = (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
    (DerivedCategory.singleFunctor A' 0).map f.inv ≫ hS'.singleδ ≫
      ((DerivedCategory.singleFunctor A' 0).map (R'.map h.hom))⟦(1 : ℤ)⟧'
  change (hS.map_of_exact F).singleδ ≫
      ((DerivedCategory.singleFunctor A' 0).map j)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor A' 0).map f.inv ≫ hS'.singleδ at hk
  rw [← reassoc_of% hk]
  simp only [← (shiftFunctor (DerivedCategory A') (1 : ℤ)).map_comp,
    ← CategoryTheory.Functor.map_comp]
  dsimp only [j]
  rw [Category.assoc, ← R'.map_comp, Iso.inv_hom_id, R'.map_id]
  erw [Category.comp_id]
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
private theorem quotient_square
    (X : A) (X' : A') (Y : B) (Y' : B')
    (i : X ⟶ R.obj Y) (i' : X' ⟶ R'.obj Y') (f : X' ≅ F.obj X) (q : Y' ≅ G.obj Y)
    (hp : f.hom ≫ F.map i = i' ≫ R'.map q.hom ≫ ρ.inv.app Y) :
    F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map i ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app
        ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      R'.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor A' 0).map f.inv ≫
      (DerivedCategory.singleFunctor A' 0).map i' ≫
      (R'.mapDerivedCategorySingleFunctor 0).inv.app Y' ≫
      R'.mapDerivedCategory.map ((DerivedCategory.singleFunctor B' 0).map q.hom) := by
  have h : F.map i ≫ ρ.hom.app Y = f.inv ≫ i' ≫ R'.map q.hom := by
    apply (cancel_epi f.hom).1
    rw [← Category.assoc, hp]
    simp only [Category.assoc, Iso.inv_hom_id_app,
      Iso.hom_inv_id_assoc]
    erw [Category.comp_id]
  apply (cancel_mono ((R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y))).1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [square_single R F G R' ρ Y]
  rw [← F.mapDerivedCategory.map_comp_assoc
    ((R.mapDerivedCategorySingleFunctor 0).inv.app Y)
    ((R.mapDerivedCategorySingleFunctor 0).hom.app Y), Iso.inv_hom_id_app,
    F.mapDerivedCategory.map_id, Category.id_comp]
  erw [reassoc_of% ((F.mapDerivedCategorySingleFunctor 0).hom.naturality i)]
  erw [(R'.mapDerivedCategorySingleFunctor 0).hom.naturality q.hom]
  rw [Iso.inv_hom_id_app_assoc]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [h]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map]
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R') (θ : L ⋙ G ≅ F ⋙ L')
  (hθ : ∀ X, a'.unit.app (F.obj X) ≫ R'.map (θ.inv.app X) =
    F.map (a.unit.app X) ≫ ρ.hom.app (L.obj X))
include hθ in
private theorem normalized_exchange
    (X : A) (X' : A') (Y : B) (Y' : B') (d : F.obj X ⟶ X') (g : G.obj Y ⟶ Y')
    (i : L.obj X ⟶ Y) (i' : L'.obj X' ⟶ Y')
    (f : X ⟶ R.obj Y) (f' : X' ⟶ R'.obj Y')
    (hi : a.unit.app X ≫ R.map i = f) (hi' : a'.unit.app X' ≫ R'.map i' = f')
    (hf : F.map f ≫ ρ.hom.app Y ≫ R'.map g = d ≫ f') :
    G.map i ≫ g = θ.hom.app X ≫ L'.map d ≫ i' := by
  apply (cancel_epi (θ.inv.app X)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (a'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, hθ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρ.hom.naturality i)]
  rw [← F.map_comp_assoc, hi]
  rw [hf]
  rw [← reassoc_of% (a'.unit.naturality d), hi']
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (L : A ⥤ B) (L' : A' ⥤ B') (F : A ⥤ A') (G : B ⥤ B')
  [L.CommShift ℤ] [L'.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (θ : L ⋙ G ≅ F ⋙ L') [NatTrans.CommShift θ.hom ℤ]
  {X₁ X₃ : A} {X₁' X₃' : A'} {H Q : B} {H' Q' : B'}
  (t₁ : F.obj X₁ ⟶ X₁') (t₃ : F.obj X₃ ⟶ X₃')
  (sH : G.obj H ⟶ H') (sQ : G.obj Q ⟶ Q')
  (δ : ShiftedHom X₃ X₁ (1 : ℤ)) (δ' : ShiftedHom X₃' X₁' (1 : ℤ))
  (aF : L.obj X₃ ≅ Q) (aF' : L'.obj X₃' ≅ Q')
  (aB : ShiftedHom (L.obj X₁) H (1 : ℤ))
  (aB' : ShiftedHom (L'.obj X₁') H' (1 : ℤ))
  (hF : G.map aF.hom ≫ sQ = θ.hom.app X₃ ≫ L'.map t₃ ≫ aF'.hom)
  (hB : aB.map G ≫ sH⟦(1 : ℤ)⟧' = θ.hom.app X₁ ≫ L'.map t₁ ≫ aB')
  (hδ : δ.map F ≫ t₁⟦(1 : ℤ)⟧' = t₃ ≫ δ')
include hF hB hδ in
private theorem boundary_transport :
    ShiftedHom.map (aF.inv ≫ (δ.map L).comp aB (show (1 : ℤ) + 1 = 2 from rfl)) G ≫
      sH⟦(2 : ℤ)⟧' =
    sQ ≫ aF'.inv ≫ (δ'.map L').comp aB' (show (1 : ℤ) + 1 = 2 from rfl) := by
  have ht : (δ.map L).map G ≫ (θ.hom.app X₁)⟦(1 : ℤ)⟧' =
      θ.hom.app X₃ ≫ (δ.map F).map L' := by
    have h := ShiftedHom.map_naturality δ θ.hom
    simpa only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using h
  have hd : (δ.map F).map L' ≫ (L'.map t₁)⟦(1 : ℤ)⟧' =
      L'.map t₃ ≫ δ'.map L' := by
    change (L'.map (δ.map F) ≫ (L'.commShiftIso (1 : ℤ)).hom.app (F.obj X₁)) ≫
        (L'.map t₁)⟦(1 : ℤ)⟧' =
      L'.map t₃ ≫ L'.map δ' ≫ (L'.commShiftIso (1 : ℤ)).hom.app X₁'
    rw [Category.assoc, ← L'.commShiftIso_hom_naturality]
    rw [← L'.map_comp_assoc, hδ, CategoryTheory.Functor.map_comp, Category.assoc]
  have hi : ((δ.map L).comp aB (show (1 : ℤ) + 1 = 2 from rfl)).map G ≫
      sH⟦(2 : ℤ)⟧' =
      θ.hom.app X₃ ≫ L'.map t₃ ≫ (δ'.map L').comp aB' rfl := by
    rw [ShiftedHom.map_comp]
    dsimp only [ShiftedHom.comp]
    have hs := (shiftFunctorAdd' B' (1 : ℤ) 1 2 rfl).inv.naturality sH
    dsimp only [Functor.comp_map] at hs
    simp only [Category.assoc]
    rw [← hs]
    rw [← (shiftFunctor B' (1 : ℤ)).map_comp_assoc, hB]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% ht, reassoc_of% hd]
    rfl
  apply (cancel_epi (G.map aF.hom)).1
  dsimp only [ShiftedHom.map]
  rw [CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  rw [← G.map_comp, Iso.hom_inv_id, G.map_id, Category.id_comp]
  rw [hF]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [ShiftedHom.map, Category.assoc] using! hi
end

section NormalizedBoundaries
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B') [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  (θ : L ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L')
  [NatTrans.CommShift θ.hom ℤ]
  (hθ : ∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
    R'.mapDerivedCategory.map (θ.inv.app X) =
    F.mapDerivedCategory.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (n : ℕ) (S : ShortComplex A) (S' : ShortComplex A')
  (hS : S.ShortExact) (hS' : S'.ShortExact)
  (H Q : B) (H' Q' : B') (i : R.obj H ⟶ S.X₁) (i' : R'.obj H' ⟶ S'.X₁)
  (wi : i ≫ (n • 𝟙 S.X₁) = 0) (wi' : i' ≫ (n • 𝟙 S'.X₁) = 0)
  (hK : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact)
  (hK' : (ShortComplex.mk i' (n • 𝟙 S'.X₁) wi').ShortExact)
  (p : S.X₃ ⟶ R.obj Q) (p' : S'.X₃ ⟶ R'.obj Q')
  (aF : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≅
    (DerivedCategory.singleFunctor B 0).obj Q)
  (aF' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≅
    (DerivedCategory.singleFunctor B' 0).obj Q')
  (aB : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≅
    ((DerivedCategory.singleFunctor B 0).obj H)⟦(1 : ℤ)⟧)
  (aB' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≅
    ((DerivedCategory.singleFunctor B' 0).obj H')⟦(1 : ℤ)⟧)
  (huF : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫
    R.mapDerivedCategory.map aF.hom ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Q =
    (DerivedCategory.singleFunctor A 0).map p)
  (huF' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≫
    R'.mapDerivedCategory.map aF'.hom ≫ (R'.mapDerivedCategorySingleFunctor 0).hom.app Q' =
    (DerivedCategory.singleFunctor A' 0).map p')
  (huB : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≫
    R.mapDerivedCategory.map aB.hom =
      hK.singleδ ≫ ((R.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(1 : ℤ)⟧' ≫
      (R.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B 0).obj H))
  (huB' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≫
    R'.mapDerivedCategory.map aB'.hom =
      hK'.singleδ ≫ ((R'.mapDerivedCategorySingleFunctor 0).inv.app H')⟦(1 : ℤ)⟧' ≫
      (R'.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B' 0).obj H'))
  (f : S' ≅ F.mapShortComplex.obj S) (h : H' ≅ G.obj H) (q : Q' ≅ G.obj Q)
  (hi : i' ≫ f.hom.τ₁ = R'.map h.hom ≫ ρ.inv.app H ≫ F.map i)
  (hp : f.hom.τ₃ ≫ F.map p = p' ≫ R'.map q.hom ≫ ρ.inv.app Q)

include hθ huF huF' huB huB' hi hp in
/-- Normalized quotient and Kummer identifications, and their degree-two boundary, commute
with a shift-compatible exact adjunction comparison.
Source: Cartier proof, paragraphs 4 and 5; Stacks Project, Tag 0152
(blueprint: lem-sfb-normalized-scalar-boundary-naturality).
Proof: apply the target adjunction to each identification square. Its mate unit identity
reduces the quotient square to the given quotient equation and the natural single-complex
comparison. The Kummer square reduces to the canonical connecting morphism of the mapped
multiplication sequence. The given kernel equation defines a morphism of these sequences;
naturality of their distinguished triangles proves the required connecting-morphism square.
Exact functors preserve this canonical morphism, including its sign. For the final square,
write the boundary as the composition of the inverse quotient identification, the mapped
extension class, and the Kummer identification in shifted Hom. Functoriality and associativity
of shifted composition, together with naturality of the comparison and the two squares just
proved, give the asserted degree-two equality. -/
theorem CategoryTheory.normalizedScalarBoundaryNaturality :
    let b := aF.inv ≫ (ShiftedHom.map hS.singleδ L).comp aB.hom (show (1 : ℤ) + 1 = 2 from rfl)
    let b' := aF'.inv ≫ (ShiftedHom.map hS'.singleδ L').comp aB'.hom
      (show (1 : ℤ) + 1 = 2 from rfl)
    (G.mapDerivedCategory.map aF.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app Q =
      θ.hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫
        L'.map ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃) ≫
        L'.map ((DerivedCategory.singleFunctor A' 0).map f.inv.τ₃) ≫ aF'.hom ≫
        (DerivedCategory.singleFunctor B' 0).map q.hom) ∧
    (G.mapDerivedCategory.map aB.hom ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor B 0).obj H) ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(1 : ℤ)⟧' =
      θ.hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≫
        L'.map ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁) ≫
        L'.map ((DerivedCategory.singleFunctor A' 0).map f.inv.τ₁) ≫ aB'.hom ≫
        ((DerivedCategory.singleFunctor B' 0).map h.hom)⟦(1 : ℤ)⟧') ∧
    (ShiftedHom.map b G.mapDerivedCategory ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' =
      (G.mapDerivedCategorySingleFunctor 0).hom.app Q ≫
        (DerivedCategory.singleFunctor B' 0).map q.inv ≫ b' ≫
        ((DerivedCategory.singleFunctor B' 0).map h.hom)⟦(2 : ℤ)⟧') := by
  dsimp only
  have hu (X : A) (Y : B)
      (a : L.obj ((DerivedCategory.singleFunctor A 0).obj X) ⟶
        (DerivedCategory.singleFunctor B 0).obj Y) (p : X ⟶ R.obj Y)
      (ha : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
        R.mapDerivedCategory.map a ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Y =
        (DerivedCategory.singleFunctor A 0).map p) :
      ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
        R.mapDerivedCategory.map a =
      (DerivedCategory.singleFunctor A 0).map p ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app Y := by
    rw [← ha]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hnF := hu S.X₃ Q aF.hom p huF
  have hnF' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≫
      R'.mapDerivedCategory.map aF'.hom = (DerivedCategory.singleFunctor A' 0).map p' ≫
        (R'.mapDerivedCategorySingleFunctor 0).inv.app Q' := by
    rw [← huF']
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hF := normalized_exchange ad ad' F.mapDerivedCategory G.mapDerivedCategory
    (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ) θ hθ
    ((DerivedCategory.singleFunctor A 0).obj S.X₃)
    ((DerivedCategory.singleFunctor A' 0).obj S'.X₃)
    ((DerivedCategory.singleFunctor B 0).obj Q)
    ((DerivedCategory.singleFunctor B' 0).obj (G.obj Q))
    ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₃ ≫
      (DerivedCategory.singleFunctor A' 0).map f.inv.τ₃)
    ((G.mapDerivedCategorySingleFunctor 0).hom.app Q) aF.hom
    (aF'.hom ≫ (DerivedCategory.singleFunctor B' 0).map q.hom)
    _ _ hnF (by
      simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
      rw [hnF'])
    (by simpa only [Category.assoc] using!
      quotient_square R F G R' ρ S.X₃ S'.X₃ Q Q' p p' (ShortComplex.π₃.mapIso f) q hp)
  have hB := normalized_exchange ad ad' F.mapDerivedCategory G.mapDerivedCategory
    (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ) θ hθ
    ((DerivedCategory.singleFunctor A 0).obj S.X₁)
    ((DerivedCategory.singleFunctor A' 0).obj S'.X₁)
    (((DerivedCategory.singleFunctor B 0).obj H)⟦(1 : ℤ)⟧)
    (((DerivedCategory.singleFunctor B' 0).obj (G.obj H))⟦(1 : ℤ)⟧)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app S.X₁ ≫
      (DerivedCategory.singleFunctor A' 0).map f.inv.τ₁)
    ((G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor B 0).obj H) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(1 : ℤ)⟧') aB.hom
    (aB'.hom ≫ ((DerivedCategory.singleFunctor B' 0).map h.hom)⟦(1 : ℤ)⟧')
    _ _ huB (by
      simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
      rw [huB'])
    (by simpa only [restrictionBoundary, Category.assoc] using!
      (kummer_square R F G R' ρ n S.X₁ S'.X₁ H H' i i' wi wi' hK hK'
        (ShortComplex.π₁.mapIso f) h hi))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hF hB
  refine ⟨hF, hB, ?_⟩
  let t₁ := (F.mapDerivedCategorySingleFunctor 0).app S.X₁ ≪≫
    (DerivedCategory.singleFunctor A' 0).mapIso (ShortComplex.π₁.mapIso f).symm
  let t₃ := (F.mapDerivedCategorySingleFunctor 0).app S.X₃ ≪≫
    (DerivedCategory.singleFunctor A' 0).mapIso (ShortComplex.π₃.mapIso f).symm
  let sH := (G.mapDerivedCategorySingleFunctor 0).app H ≪≫
    (DerivedCategory.singleFunctor B' 0).mapIso h.symm
  let sQ := (G.mapDerivedCategorySingleFunctor 0).app Q ≪≫
    (DerivedCategory.singleFunctor B' 0).mapIso q.symm
  have hFa : G.mapDerivedCategory.map aF.hom ≫ sQ.hom =
      θ.hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫
        L'.map t₃.hom ≫ aF'.hom := by
    have hh := congrArg (fun z ↦ z ≫ (DerivedCategory.singleFunctor B' 0).map q.inv) hF
    dsimp only [sQ, t₃, Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [Category.assoc] at hh
    erw [← (DerivedCategory.singleFunctor B' 0).map_comp q.hom q.inv,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] at hh
    simpa only using! hh
  have hBa : ShiftedHom.map aB.hom G.mapDerivedCategory ≫ sH.hom⟦(1 : ℤ)⟧' =
      θ.hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≫
        L'.map t₁.hom ≫ aB'.hom := by
    have hh := congrArg (fun z ↦ z ≫
      ((DerivedCategory.singleFunctor B' 0).map h.inv)⟦(1 : ℤ)⟧') hB
    dsimp only [sH, t₁, Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, ShiftedHom.map]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [Category.assoc] at hh
    erw [← (shiftFunctor (DerivedCategory B') (1 : ℤ)).map_comp
        ((DerivedCategory.singleFunctor B' 0).map h.hom)
        ((DerivedCategory.singleFunctor B' 0).map h.inv),
      ← (DerivedCategory.singleFunctor B' 0).map_comp h.hom h.inv,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.comp_id] at hh
    simpa only using! hh
  have hd : ShiftedHom.map hS.singleδ F.mapDerivedCategory ≫ t₁.hom⟦(1 : ℤ)⟧' =
      t₃.hom ≫ hS'.singleδ := by
    have hm := (ShortComplex.ShortExact.singleTriangle.map (hS.map_of_exact F) hS'
      f.inv).comm₃
    have hfδ := hS.mapShiftedHom_singleδ' F
    dsimp only [ShiftedHom.map] at hfδ
    simp only [Category.assoc] at hfδ
    apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app S.X₃)).1
    dsimp only [t₁, t₃, ShiftedHom.map, Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [reassoc_of% hfδ, Iso.inv_hom_id_app_assoc]
    exact hm
  have hb := boundary_transport L L' F.mapDerivedCategory G.mapDerivedCategory θ
    t₁.hom t₃.hom sH.hom sQ.hom hS.singleδ hS'.singleδ aF aF' aB.hom aB'.hom
    hFa hBa hd
  have hh := congrArg (fun z ↦ z ≫
    ((DerivedCategory.singleFunctor B' 0).map h.hom)⟦(2 : ℤ)⟧') hb
  simp only [sH, sQ, Iso.trans_hom, Iso.app_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp, Category.assoc] at hh
  erw [← (shiftFunctor (DerivedCategory B') (2 : ℤ)).map_comp
    ((DerivedCategory.singleFunctor B' 0).map h.inv)
    ((DerivedCategory.singleFunctor B' 0).map h.hom),
    ← (DerivedCategory.singleFunctor B' 0).map_comp h.inv h.hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at hh
  simpa only [Category.assoc] using! hh
end NormalizedBoundaries
