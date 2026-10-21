/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Derived tensor of modules computes Tor

Source: Stacks Project, Tags 00LY, 00LZ and 0H7Z.
(blueprint: lem-kun-derived-module-tor-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private theorem resolution_tensor_nat (P P' L L' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P')
    (f : P ⟶ P') (g : L ⟶ L') :
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (QObjTensorQObjIsoOfKFlatLeft P' L' hP').hom =
      (QObjTensorQObjIsoOfKFlatLeft P L hP).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have h₁ := Functor.LaxMonoidal.μ_natural (Qh (C := ModuleCat.{u} R)) (q.map f) (q.map g)
  have h₂ := Functor.LaxMonoidal.μ_natural q f g
  have h₃ := (quotientCompQhIso (ModuleCat.{u} R)).hom.naturality (f ⊗ₘ g)
  have h₄ := (quotientCompQhIso (ModuleCat.{u} R)).inv.naturality f
  have h₅ := (quotientCompQhIso (ModuleCat.{u} R)).inv.naturality g
  dsimp at h₁ h₂ h₃ h₄ h₅
  simp only [QObjTensorQObjIsoOfKFlatLeft, Iso.trans_hom, tensorIso_hom, Iso.app_hom,
    Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  have key : (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
      ((quotientCompQhIso (ModuleCat.{u} R)).inv.app P' ⊗ₘ
        (quotientCompQhIso (ModuleCat.{u} R)).inv.app L') =
      ((quotientCompQhIso (ModuleCat.{u} R)).inv.app P ⊗ₘ
        (quotientCompQhIso (ModuleCat.{u} R)).inv.app L) ≫
          (Qh.map (q.map f) ⊗ₘ Qh.map (q.map g)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₄, h₅]
  rw [reassoc_of% key]
  dsimp only [tensorLeftCounit, Functor.bifunctorCounit₁,
    Functor.LaxMonoidal.μNatTrans]
  rw [reassoc_of% h₁, ← h₃, Functor.Monoidal.μIso_hom, ← Qh.map_comp_assoc,
    h₂, Qh.map_comp_assoc, Functor.Monoidal.μIso_hom]


omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem resolution_single_nat (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (f : P ⟶ Q)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (f ⊗ₘ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N' Q).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N P).hom ≫
        (((tensorRight N).mapHomologicalComplex (.up ℤ)).map f ≫
          ((NatTrans.mapHomologicalComplex
            ((tensoringRight (ModuleCat R)).map g) (.up ℤ)).app Q)) := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N P).inv).1
  apply (cancel_mono
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N' Q).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    CochainComplex.mapBifunctorSingle₁XIso, ComplexShape.π_def, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Functor.flip_map_app, curriedTensor_obj_map, Functor.flip_obj_map,
    curriedTensor_map_app, eqToHom_whiskerRight, Iso.symm_mk, Iso.trans_inv, Iso.symm_inv,
    Category.comp_id, Category.assoc, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom_assoc,
    ComplexShape.σ_def, mul_zero, Int.negOnePow_zero, one_smul, NatTrans.naturality_assoc,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  change _ ≫ _ ≫ (HomologicalComplex.mapBifunctorMap f
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)
    (curriedTensor (ModuleCat R)) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self,
    ← tensorHom_id, ← id_tensorHom,
    ]



private def resolution_single_iso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (N : ModuleCat.{u} R) :
    DerivedCategory.Q.obj P ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj N ≅
      DerivedCategory.Q.obj (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P) :=
  tensorIso (Iso.refl _) ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N) ≪≫
    QObjTensorQObjIsoOfKFlatLeft P _ hP ≪≫
      DerivedCategory.Q.mapIso
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat R)) N P)

private theorem resolution_single_iso_nat (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q)
    (f : P ⟶ Q) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (DerivedCategory.Q.map f ⊗ₘ (singleFunctor (ModuleCat.{u} R) 0).map g) ≫
        (resolution_single_iso Q hQ N').hom =
      (resolution_single_iso P hP N).hom ≫
        DerivedCategory.Q.map
          (((tensorRight N).mapHomologicalComplex (.up ℤ)).map f ≫
            ((NatTrans.mapHomologicalComplex
              ((tensoringRight (ModuleCat R)).map g) (.up ℤ)).app Q)) := by
  have hS := (singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.naturality g
  dsimp at hS
  have key : (DerivedCategory.Q.map f ⊗ₘ (singleFunctor (ModuleCat.{u} R) 0).map g) ≫
      (𝟙 _ ⊗ₘ ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N').hom) =
      (𝟙 _ ⊗ₘ ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N).hom) ≫
        (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (fun k ↦ DerivedCategory.Q.map f ⊗ₘ k) hS
  simp only [resolution_single_iso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% key, reassoc_of% (resolution_tensor_nat P Q _ _ hP hQ f
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g))]
  have hC := congrArg DerivedCategory.Q.map (resolution_single_nat P Q f g)
  simp only [Functor.map_comp] at hC
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ (𝟙 _ ⊗ₘ
      ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N).hom) ≫
        (QObjTensorQObjIsoOfKFlatLeft P _ hP).hom ≫ k) hC


private abbrev resolutionComplex (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (projectiveResolution M).complex.extend (ComplexShape.embeddingUpIntLE 0)

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem resolutionIsKFlat (M : ModuleCat.{u} R) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (resolutionComplex M) := by
  have hbounded : (resolutionComplex M).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (projectiveResolution M).complex.isZero_extend_X _ i
      (by intro j; change 0 - (j : ℤ) ≠ i; omega)
  have hflat (i : ℤ) : ObjectProperty.flat ((resolutionComplex M).X i) := by
    dsimp only [resolutionComplex]
    apply (ModuleCat.flat_iff_flat _).2
    infer_instance
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℤ)).symm
  have (X : ModuleCat.{u} R) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat R)).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight X))
  exact CochainComplex.kFlat_of_isStrictlyLE_of_flat (resolutionComplex M) 0 hflat

private def resolution_augmentation (M : ModuleCat.{u} R) :
    resolutionComplex M ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
  HomologicalComplex.extendMap (projectiveResolution M).π
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0) M
      0 0 (by simp)).hom

private instance (M : ModuleCat.{u} R) : QuasiIso (resolution_augmentation M) := by
  dsimp [resolution_augmentation]
  infer_instance

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem resolution_augmentation_nat {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    HomologicalComplex.extendMap
        (ProjectiveResolution.lift f (projectiveResolution M) (projectiveResolution M'))
        (ComplexShape.embeddingUpIntLE 0) ≫ resolution_augmentation M' =
      resolution_augmentation M ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f := by
  dsimp only [resolution_augmentation]
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    ProjectiveResolution.lift_commutes, HomologicalComplex.extendMap_comp, Category.assoc]
  have he : HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat.{u} R)).map f)
        (ComplexShape.embeddingUpIntLE 0) ≫
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0) M'
        0 0 (by simp)).hom =
      (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0) M
        0 0 (by simp)).hom ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f := by
    apply HomologicalComplex.to_single_hom_ext
    simp [HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendMap_f,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc]
  exact congrArg (HomologicalComplex.extendMap (projectiveResolution M).π
    (ComplexShape.embeddingUpIntLE 0) ≫ ·) he


private def resolutionIso (M : ModuleCat.{u} R) :
    DerivedCategory.Q.obj (resolutionComplex M) ≅
      (singleFunctor (ModuleCat.{u} R) 0).obj M :=
  asIso (DerivedCategory.Q.map (resolution_augmentation M)) ≪≫
    ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M).symm

private theorem resolutionIso_nat {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    DerivedCategory.Q.map (HomologicalComplex.extendMap
        (ProjectiveResolution.lift f (projectiveResolution M) (projectiveResolution M'))
        (ComplexShape.embeddingUpIntLE 0)) ≫ (resolutionIso M').hom =
      (resolutionIso M).hom ≫ (singleFunctor (ModuleCat.{u} R) 0).map f := by
  have h := congrArg DerivedCategory.Q.map (resolution_augmentation_nat f)
  simp only [Functor.map_comp] at h
  simp only [resolutionIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc]
  rw [reassoc_of% h]
  exact congrArg (DerivedCategory.Q.map (resolution_augmentation M) ≫ ·)
    ((singleFunctorIsoCompQ (ModuleCat.{u} R) 0).inv.naturality f)


private def resolution_tensor_model (M N : ModuleCat.{u} R) :
    (singleFunctor (ModuleCat.{u} R) 0).obj M ⊗
        (singleFunctor (ModuleCat.{u} R) 0).obj N ≅
      DerivedCategory.Q.obj
        (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj (resolutionComplex M)) :=
  whiskerRightIso (resolutionIso M).symm _ ≪≫
    resolution_single_iso (resolutionComplex M) (resolutionIsKFlat M) N

private theorem resolution_tensor_model_nat {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((singleFunctor (ModuleCat.{u} R) 0).map f ⊗ₘ
      (singleFunctor (ModuleCat.{u} R) 0).map g) ≫ (resolution_tensor_model M' N').hom =
      (resolution_tensor_model M N).hom ≫ DerivedCategory.Q.map
        (((tensorRight N).mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.extendMap (ProjectiveResolution.lift f
              (projectiveResolution M) (projectiveResolution M'))
              (ComplexShape.embeddingUpIntLE 0)) ≫
          ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
            (.up ℤ)).app (resolutionComplex M'))) := by
  have he := resolutionIso_nat f
  have he' : (singleFunctor (ModuleCat.{u} R) 0).map f ≫
      (resolutionIso M').inv =
      (resolutionIso M).inv ≫ DerivedCategory.Q.map
        (HomologicalComplex.extendMap (ProjectiveResolution.lift f
          (projectiveResolution M) (projectiveResolution M'))
          (ComplexShape.embeddingUpIntLE 0)) := by
    rw [← cancel_epi (resolutionIso M).hom,
      ← cancel_mono (resolutionIso M').hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using he.symm
  simp only [resolution_tensor_model, Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom,
    Category.assoc]
  have key : ((singleFunctor (ModuleCat.{u} R) 0).map f ⊗ₘ
        (singleFunctor (ModuleCat.{u} R) 0).map g) ≫
      (resolutionIso M').inv ▷ (singleFunctor (ModuleCat.{u} R) 0).obj N' =
      (resolutionIso M).inv ▷ (singleFunctor (ModuleCat.{u} R) 0).obj N ≫
        (DerivedCategory.Q.map (HomologicalComplex.extendMap (ProjectiveResolution.lift f
          (projectiveResolution M) (projectiveResolution M'))
          (ComplexShape.embeddingUpIntLE 0)) ⊗ₘ (singleFunctor (ModuleCat.{u} R) 0).map g) := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp, he']
  rw [reassoc_of% key]
  have hn := resolution_single_iso_nat (resolutionComplex M) (resolutionComplex M')
    (resolutionIsKFlat M) (resolutionIsKFlat M')
    (HomologicalComplex.extendMap (ProjectiveResolution.lift f
      (projectiveResolution M) (projectiveResolution M'))
      (ComplexShape.embeddingUpIntLE 0)) g
  simpa only [Category.assoc] using congrArg
    ((resolutionIso M).inv ▷ (singleFunctor (ModuleCat.{u} R) 0).obj N ≫ ·) hn

private def resolution_tor_iso (M N : ModuleCat.{u} R) (j : ℕ) :
    (homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).obj
      ((singleFunctor (ModuleCat.{u} R) 0).obj M ⊗
        (singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
      (((Tor' (ModuleCat.{u} R) j).obj M).obj N) :=
  (homologyFunctor (ModuleCat R) (-(j : ℤ))).mapIso (resolution_tensor_model M N) ≪≫
    (homologyFunctorFactors (ModuleCat R) (-(j : ℤ))).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(j : ℤ))).mapIso
      (((ComplexShape.embeddingUpIntLE 0).mapExtendFunctorNatIso (tensorRight N)).app
        (projectiveResolution M).complex) ≪≫
    (((tensorRight N).mapHomologicalComplex (.down ℕ)).obj
      (projectiveResolution M).complex).extendHomologyIso (ComplexShape.embeddingUpIntLE 0)
      (show (ComplexShape.embeddingUpIntLE 0).f j = -(j : ℤ) by
        change 0 - (j : ℤ) = _; omega) ≪≫
    ((projectiveResolution M).isoLeftDerivedObj (tensorRight N) j).symm


private theorem resolution_tor_iso_first {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (N : ModuleCat.{u} R) (j : ℕ) :
    (homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).map
        ((singleFunctor (ModuleCat.{u} R) 0).map f ▷
          (singleFunctor (ModuleCat.{u} R) 0).obj N) ≫ (resolution_tor_iso M' N j).hom =
      (resolution_tor_iso M N j).hom ≫ ((Tor' (ModuleCat.{u} R) j).map f).app N := by
  let φ := ProjectiveResolution.lift f (projectiveResolution M) (projectiveResolution M')
  let e := ComplexShape.embeddingUpIntLE 0
  let F := tensorRight N
  let H := homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))
  let Hc := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(j : ℤ))
  have h₁ : H.map ((singleFunctor (ModuleCat.{u} R) 0).map f ▷
        (singleFunctor (ModuleCat.{u} R) 0).obj N) ≫
      H.map (resolution_tensor_model M' N).hom =
      H.map (resolution_tensor_model M N).hom ≫
        H.map (DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap φ e))) := by
    simpa [Functor.map_comp] using congrArg H.map (resolution_tensor_model_nat f (𝟙 N))
  have h₂ := (homologyFunctorFactors (ModuleCat.{u} R) (-(j : ℤ))).hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap φ e))
  have h₃ := congrArg Hc.map ((e.mapExtendFunctorNatIso F).hom.naturality φ)
  simp only [Functor.map_comp] at h₃
  have h₄ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (.down ℕ)).map φ) e
    (show e.f j = -(j : ℤ) by change 0 - (j : ℤ) = _; omega)
  have h₅ := ProjectiveResolution.isoLeftDerivedObj_inv_naturality f
    (projectiveResolution M) (projectiveResolution M') φ
    (ProjectiveResolution.lift_commutes_zero f _ _) F j
  dsimp only [resolution_tor_iso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  dsimp only [resolutionComplex]
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄,
    ← h₅]
  rfl


private theorem resolution_tensor_model_second (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((singleFunctor (ModuleCat.{u} R) 0).obj M ◁
      (singleFunctor (ModuleCat.{u} R) 0).map g) ≫ (resolution_tensor_model M N').hom =
      (resolution_tensor_model M N).hom ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
          (.up ℤ)).app (resolutionComplex M)) := by
  have hn : DerivedCategory.Q.obj (resolutionComplex M) ◁
        (singleFunctor (ModuleCat.{u} R) 0).map g ≫
      (resolution_single_iso (resolutionComplex M) (resolutionIsKFlat M) N').hom =
      (resolution_single_iso (resolutionComplex M) (resolutionIsKFlat M) N).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat R)).map g) (.up ℤ)).app (resolutionComplex M)) := by
    simpa using resolution_single_iso_nat (resolutionComplex M) (resolutionComplex M)
      (resolutionIsKFlat M) (resolutionIsKFlat M) (𝟙 _) g
  simp only [resolution_tensor_model, Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [MonoidalCategory.whisker_exchange_assoc, hn]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem resolution_map_extend_second
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
        (.up ℤ)).app (K.extend (ComplexShape.embeddingUpIntLE 0))) ≫
      (K.mapExtendIso (ComplexShape.embeddingUpIntLE 0) (tensorRight N')).hom =
      (K.mapExtendIso (ComplexShape.embeddingUpIntLE 0) (tensorRight N)).hom ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex
          ((tensoringRight (ModuleCat R)).map g) (.down ℕ)).app K)
          (ComplexShape.embeddingUpIntLE 0) := by
  let e := ComplexShape.embeddingUpIntLE 0
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : ∃ j, e.f j = i
  · obtain ⟨j, rfl⟩ := hi
    dsimp only [e]
    simp only [HomologicalComplex.extend, HomologicalComplex.mapExtendIso,
      HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.flip_map_app, curriedTensor_obj_map,
      HomologicalComplex.Hom.isoOfComponents_hom_f,
      HomologicalComplex.mapExtendX_hom_eq _ _ ((ComplexShape.embeddingUpIntLE 0).r_f j),
      Functor.flip_obj_obj, curriedTensor_obj_obj, eqToIso.hom, ComplexShape.embeddingUpIntLE_f,
      zero_sub, neg_inj, Nat.cast_inj, HomologicalComplex.extendMap_f,
      HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso, eqToIso.inv, eqToHom_trans_assoc]
    have hr := (ComplexShape.embeddingUpIntLE 0).r_f j
    apply (cancel_mono (eqToHom (congrArg
      (HomologicalComplex.extend.X
        (((tensorRight N').mapHomologicalComplex (.down ℕ)).obj K)) hr))).1
    simpa only [HomologicalComplex.extend.X, Functor.mapHomologicalComplex_obj_X,
      tensorRight, curriedTensor, Functor.flip_obj_obj, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id] using
      eqToHom_naturality (fun x : Option ℕ ↦ HomologicalComplex.extend.X K x ◁ g) hr
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ e i (by simpa only [not_exists] using hi)



private theorem resolution_tor_iso_second (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (j : ℕ) :
    (homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).map
        ((singleFunctor (ModuleCat.{u} R) 0).obj M ◁
          (singleFunctor (ModuleCat.{u} R) 0).map g) ≫ (resolution_tor_iso M N' j).hom =
      (resolution_tor_iso M N j).hom ≫ ((Tor' (ModuleCat.{u} R) j).obj M).map g := by
  let e := ComplexShape.embeddingUpIntLE 0
  let H := homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))
  let Hc := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(j : ℤ))
  let α := (tensoringRight (ModuleCat R)).map g
  have h₁ := congrArg H.map (resolution_tensor_model_second M g)
  simp only [Functor.map_comp] at h₁
  have h₂ := (homologyFunctorFactors (ModuleCat.{u} R) (-(j : ℤ))).hom.naturality
    ((NatTrans.mapHomologicalComplex α (.up ℤ)).app (resolutionComplex M))
  have h₃ := congrArg Hc.map (resolution_map_extend_second (projectiveResolution M).complex g)
  simp only [Functor.map_comp] at h₃
  have h₄ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((NatTrans.mapHomologicalComplex α (.down ℕ)).app (projectiveResolution M).complex) e
    (show e.f j = -(j : ℤ) by change 0 - (j : ℤ) = _; omega)
  have h₅ := ProjectiveResolution.leftDerived_app_eq α (projectiveResolution M) j
  dsimp only [resolution_tor_iso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  dsimp only [resolutionComplex]
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄]
  simp only [Tor'_obj_map]
  rw [h₅]
  simp only [Iso.inv_hom_id_assoc]
  rfl


variable (R) in
/-- Cohomology of the derived tensor of single modules, as a bifunctor.
Source: Stacks Project, Tag 0H7Z (blueprint: lem-kun-derived-module-tor-comparison). -/
noncomputable def kunnethModuleTensorHomology (n : ℤ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M :=
    { obj N := (homologyFunctor (ModuleCat.{u} R) n).obj
        ((singleFunctor (ModuleCat.{u} R) 0).obj M ⊗
          (singleFunctor (ModuleCat.{u} R) 0).obj N)
      map g := (homologyFunctor (ModuleCat.{u} R) n).map
        ((singleFunctor (ModuleCat.{u} R) 0).obj M ◁
          (singleFunctor (ModuleCat.{u} R) 0).map g)
      map_id N := by simp
      map_comp g h := by simp [Functor.map_comp, whiskerLeft_comp] }
  map f :=
    { app N := (homologyFunctor (ModuleCat.{u} R) n).map
        ((singleFunctor (ModuleCat.{u} R) 0).map f ▷
          (singleFunctor (ModuleCat.{u} R) 0).obj N)
      naturality {N N'} g := by
        dsimp
        rw [← Functor.map_comp, ← Functor.map_comp, whisker_exchange] }
  map_id M := by ext N; simp
  map_comp f g := by ext N; simp [Functor.map_comp, comp_whiskerRight]

/-- Derived tensor cohomology is naturally Tor, extended by zero in negative degrees.
Source: Stacks Project, Tags 00LY, 00LZ and 0H7Z.
(blueprint: lem-kun-derived-module-tor-comparison).

Proof. Extend a projective resolution of the first module to nonpositive cochain
degrees. Its flat terms make it K-flat. The augmentation and K-flat tensor comparison
identify the derived tensor with the termwise tensor of the resolution and the second
module. Apply cohomology, the extension comparison, and the projective resolution
comparison to Tor. Resolution lifts give naturality in the first module; tensor
transformations and their compatibility with extension give naturality in the second.
Positive cohomology vanishes since both single modules are bounded above by zero,
and isomorphisms between zero objects are automatically natural. -/
theorem kunnethModuleTensorHomology_tor (k : ℤ) :
    Nonempty (kunnethModuleTensorHomology R (-k) ≅
      if k < 0 then
        (Functor.const (ModuleCat.{u} R)).obj
          ((Functor.const (ModuleCat.{u} R)).obj (0 : ModuleCat.{u} R))
      else Tor' (ModuleCat.{u} R) k.toNat) := by
  classical
  by_cases hk : k < 0
  · rw [if_pos hk]
    have hz (M N : ModuleCat.{u} R) : IsZero
        (((kunnethModuleTensorHomology R (-k)).obj M).obj N) := by
      have hle := isLE_tensor ((singleFunctor (ModuleCat.{u} R) 0).obj M)
        ((singleFunctor (ModuleCat.{u} R) 0).obj N) 0 0
      exact isZero_of_isLE _ 0 (-k) (by omega) (hX := hle)
    refine ⟨NatIso.ofComponents (fun M ↦ NatIso.ofComponents
      (fun N ↦ (hz M N).isoZero) ?_) ?_⟩
    · intro N N' g
      exact (isZero_zero (ModuleCat.{u} R)).eq_of_tgt _ _
    · intro M M' f
      apply NatTrans.ext
      funext N
      exact (isZero_zero (ModuleCat.{u} R)).eq_of_tgt _ _
  · rw [if_neg hk]
    have hk' : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
    rw [← hk']
    refine ⟨NatIso.ofComponents (fun M ↦ NatIso.ofComponents
      (fun N ↦ resolution_tor_iso M N k.toNat) ?_) ?_⟩
    · intro N N' g
      exact resolution_tor_iso_second _ g k.toNat
    · intro M M' f
      apply NatTrans.ext
      funext N
      exact resolution_tor_iso_first f N k.toNat


end DerivedCategory
