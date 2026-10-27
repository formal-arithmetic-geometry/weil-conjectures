/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.PurityDncInvariance
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import Sheaf.SixFunctors.ComparisonOpenTensorCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Tensor coherence of the derived comparison pullback square

Source: composition coherence Step 1, compatible-DNC-charts proof Step 8.
(blueprint: lem-pur-comparison-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem pullComparison_eq (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (b : X ⟶ Y)
    (K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient b).app K =
      (Dnc.pullComparison P b K).symm := by
  have hd : Functor.mapDerivedCategoryNatIso
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) b).symm =
      (Functor.mapDerivedCategoryNatIso
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} P.Coefficient) b)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  apply Iso.ext
  simp only [ProEtale.comparisonOpenDerivedPullbackIso, ProEtale.supportComparison_eq,
    hd, Dnc.pullComparison, ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso,
    NatIso.trans_app, Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_inv, Category.assoc]

/-- The tensor square for the exact comparison between the two sites, for arbitrary
ordinary derived objects. No smooth morphism, affine chart, section or purity map
is involved.
Source: composition coherence Step 1; comparison-monoidal pullback coherence
(blueprint: lem-pur-comparison-tensor-pullback).

Proof: the underived inverse-image square g* nu* = nu* g* is monoidal: both
routes send a pair of local sections to the same tensor of their inverse images.
Apply comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso to
its derived square. Conjugate each comparison functor by the canonical exact
identification L(nu*) = D(nu*). The resulting square has pullback comparison
Dnc.pullComparison, since expanding leftDerivedFunctorCompNatIso cancels the
exact-functor identifications at both intermediate composites. The two horizontal
tensor constraints become derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso.
Move the invertible comparison tensor maps to the other sides of the equation.
This is the displayed identity, for every pair of objects of the unbounded derived
category; it requires neither constructibility nor a chosen orientation. -/
theorem comparisonTensorPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (b : X ⟶ Y)
    (K L : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    let A := ModuleCat.{u + 1} P.Coefficient
    let F := (ProEtale.comparisonUpperStar A Y).mapDerivedCategory
    let F' := (ProEtale.comparisonUpperStar A X).mapDerivedCategory
    let G := (Etale.upperStar A b).leftDerivedFunctor
    let H := (ProEtale.upperStar A b).leftDerivedFunctor
    let m := fun (B : Scheme.{u})
      (K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) ↦
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app L
    H.mapIso (m Y K L).symm ≪≫
        Dnc.pullComparison P b (((Etale.derivedTensor A Y).obj K).obj L) ≪≫
        F'.mapIso (Etale.leftDerivedUpperStarTensorIso A b K L) =
      ProEtale.leftDerivedUpperStarTensorIso A b (F.obj K) (F.obj L) ≪≫
        ((ProEtale.derivedTensor A X).mapIso (Dnc.pullComparison P b K)).app _ ≪≫
        ((ProEtale.derivedTensor A X).obj (F'.obj (G.obj K))).mapIso
          (Dnc.pullComparison P b L) ≪≫
        (m X (G.obj K) (G.obj L)).symm := by
  apply Iso.ext
  have hm (B : Scheme.{u})
      (K L : _root_.DerivedCategory
        (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
      ((ProEtale.comparisonTensorNatIso P.Coefficient B).hom.app K).app L =
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} P.Coefficient) K).hom.app L :=
    congrArg (fun a ↦ a.hom.app L) (ProEtale.comparison_tensor_app P.Coefficient B K)
  have hp (Z : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
      (ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient b).hom.app Z =
        (Dnc.pullComparison P b Z).inv := congrArg Iso.hom (pullComparison_eq P b Z)
  have hp' (Z : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
      (ProEtale.comparisonOpenDerivedPullbackIso P.Coefficient b).inv.app Z =
        (Dnc.pullComparison P b Z).hom := congrArg Iso.inv (pullComparison_eq P b Z)
  have h := ProEtale.comparison_tensor_compatible P.Coefficient b K L
  simp only [Iso.symm_inv, Iso.symm_hom, hm, hp, hp'] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  apply (cancel_epi ((ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) K).hom.app L))).1
  apply (cancel_mono ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient)
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K)).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj L))).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app,
    Etale.leftDerivedUpperStarTensorIso_hom,
    ProEtale.leftDerivedUpperStarTensorIso_hom]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]
  dsimp only [Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


end WeilConjectures.PurityFiniteSetting
