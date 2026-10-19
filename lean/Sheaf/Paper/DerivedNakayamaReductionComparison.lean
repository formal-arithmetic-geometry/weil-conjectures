/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.DerivedNakayamaResolution

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing

/-!
# Canonical integral reduction as derived tensor

Source: blueprint main-20261015, first-reduction lemma, step 1
(blueprint: det-pe-derived-nakayama-reduction-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def restrictExtendTensorIso
    {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R) :
    (Mod.comap φ).obj ((Mod.extendScalars φ).obj M) ≅
      ((Mod.comap φ).obj (Mod.regular S)) ⊗ M :=
  Mod.isoMk (Mod.extendForgetTensorObjIso φ M) (by
    dsimp only [Mod.extendForgetTensorObjIso]
    apply (cancel_epi (R ◁ Mod.extendπ φ M)).1
    change R ◁ Mod.extendπ φ M ≫ (φ ▷ _ ≫ γ[S,_]) ≫ _ = _
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, Mod.whiskerLeft_extendπ_smul_assoc]
    rw [Mod.extendπ_extendDescHom]
    rw [← whiskerLeft_comp_assoc, Mod.extendπ_extendDescHom, Mod.whiskerLeft_tensorπ_smul]
    rw [associator_inv_naturality_left_assoc]
    change _ = (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫
      Mod.tensorObjπ ((Mod.comap φ).obj (Mod.regular S)) M
    rw [comp_whiskerRight, Category.assoc])

private noncomputable def mapComapRegularIso
    {C : Type w} [Category.{v} C] [MonoidalCategory C]
    {D : Type w} [Category.{v} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    (F.mapMod R).obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap (F.map φ)).obj (Mod.regular (F.obj S)) :=
  (F.mapModComapIso φ).app (Mod.regular S) ≪≫
    (Mod.comap (F.map φ)).mapIso
      (Mod.isoMk (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id, whiskerLeft_id, Category.id_comp]))

private theorem restrictExtendDerivedComparison
    {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (K : DerivedCategory (Mod C R)) :
    Nonempty (((Mod.extendScalars φ).leftDerivedFunctor ⋙
      (Mod.comap φ).mapDerivedCategory).obj K ≅
      K ⊗ (DerivedCategory.singleFunctor (Mod C R) 0).obj
        ((Mod.comap φ).obj (Mod.regular S))) := by
  classical
  let L := DerivedCategory.Q.objPreimage K
  let eL := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, π, hπ, hflat, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat L
  have := hπ
  let e : DerivedCategory.Q.obj P ≅ K := asIso (DerivedCategory.Q.map π) ≪≫ eL
  let Ext := Mod.extendScalars φ
  let Res := Mod.comap (D := C) φ
  let B := Res.obj (Mod.regular S)
  let ei : Ext.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((Ext.mapHomologicalComplex (.up ℤ)).obj P) := by
    have := Ext.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
    exact Ext.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
      asIso (Ext.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((Ext.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso (Mod C S)).app
        ((Ext.mapHomologicalComplex (.up ℤ)).obj P)
  let et₀ : Ext ⋙ Res ≅ tensorLeft B :=
    NatIso.ofComponents (fun M ↦ restrictExtendTensorIso φ M) (by
      intro M N f
      apply Mod.hom_ext
      exact (Mod.extendForgetTensorIso φ).hom.naturality f)
  let et : Ext ⋙ Res ≅ tensorRight B := et₀ ≪≫
    BraidedCategory.tensorLeftIsoTensorRight B
  exact ⟨(Ext.leftDerivedFunctor ⋙ Res.mapDerivedCategory).mapIso e.symm ≪≫
    Res.mapDerivedCategory.mapIso ei ≪≫ Res.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex et (.up ℤ)).app P) ≪≫
    (DerivedCategory.QObjTensorSingleFunctorObjIso P hP B).symm ≪≫
    (tensorRight ((DerivedCategory.singleFunctor _ 0).obj B)).mapIso e⟩

attribute [local irreducible] upperStarFromPoint monoidal_upperStarFromPoint

/-- Restricting the actual finite-coefficient derived extension recovers the
integral derived tensor used in the coefficient resolution theorem.
Source: blueprint main-20261015, first-reduction lemma, step 1
(blueprint: det-pe-derived-nakayama-reduction-comparison).

Proof: resolve a complex representing K by a K-flat complex P. The derived-extension
counit at P is invertible, and exact restriction commutes with localization.
Restricted extension is naturally tensor with the restricted regular quotient, by
its balanced coequalizer presentation. The mapMod-comap comparison and the identity
underlying the pulled-back regular module identify that quotient with finiteModule.
The K-flat tensor model computes derived tensor with its degree-zero realization.
Compose these isomorphisms and transport through Q(P) ≅ K. No quotient flatness or
boundedness is used. -/
theorem derived_nakayama_reduction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    Nonempty (AdicCompletion.integralLevel l E X K n ≅
      (DerivedNakayama.reductionFunctor l E X (n + 1)).obj K) := by
  obtain ⟨a⟩ := restrictExtendDerivedComparison
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (R := AdicCompletion.ring l E X) (S := AdicCompletion.finiteRing l E X n)
    (AdicCompletion.quotient l E X n) K
  let b := mapComapRegularIso (upperStarFromPoint X)
    (DerivedNakayama.reductionRing l E (n + 1))
  exact ⟨a ≪≫ (tensorLeft K).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso b.symm)⟩

end AlgebraicGeometry.ProEtale
