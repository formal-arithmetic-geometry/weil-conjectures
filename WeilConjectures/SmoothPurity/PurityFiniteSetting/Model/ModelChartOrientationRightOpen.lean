/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationPowerPullback
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Open naturality of the right orientation composite -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] coefficientNoetherian coefficientExponent

private abbrev pull (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

private theorem comparison_comp (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) (f : T ⟶ R) (h : f = a ≫ b)
    (K : Etale.DerivedCategoryModule P.Coefficient R) :
    Dnc.pullComparison P f K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
            ((Etale.leftDerivedUpperStarComp _ a b f h).app K) =
      (ProEtale.leftDerivedUpperStarCongr _ h).app _ ≪≫
        (ProEtale.leftDerivedUpperStarComp _ a b).app _ ≪≫
        (pull P a).mapIso (Dnc.pullComparison P b K) ≪≫
        Dnc.pullComparison P a
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K) := by
  subst f
  apply Iso.ext
  simpa only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Functor.mapIso_hom,
    Iso.refl_hom, Iso.app_hom, NatTrans.id_app, Category.id_comp, Category.assoc] using
      Dnc.pullComparison_comp P a b K

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem comparison_square (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    (M : Etale.DerivedCategoryModule P.Coefficient Y) :
    (pull P j).mapIso (Dnc.pullComparison P f M) ≪≫
        Dnc.pullComparison P j
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj M) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.mapIso
          ((Etale.leftDerivedUpperStarComp
              (ModuleCat.{u + 1} P.Coefficient) j f).symm.app M ≪≫
            (Etale.leftDerivedUpperStarComp
              (ModuleCat.{u + 1} P.Coefficient) f' v (j ≫ f) h).app M) =
      (ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) j f).symm.app _ ≪≫
        (ProEtale.leftDerivedUpperStarCongr
          (ModuleCat.{u + 1} P.Coefficient) h).app _ ≪≫
        (ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) f' v).app _ ≪≫
        (pull P f').mapIso (Dnc.pullComparison P v M) ≪≫
        Dnc.pullComparison P f'
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj M) := by
  have hj := congrArg Iso.hom (comparison_comp P j f (j ≫ f) rfl M)
  have hv := congrArg Iso.hom (comparison_comp P f' v (j ≫ f) h M)
  simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.mapIso_hom] at hj hv
  apply Iso.ext
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) j f).hom.app _)).mp
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hj]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hv

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private abbrev ED (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  Etale.DerivedCategoryModule P.Coefficient X

attribute [local irreducible] compatibleBifunctorIso compatibleComparisonTensor
  Dnc.pullComparison ProEtale.derivedTensor Etale.derivedTensor
  ProEtale.leftDerivedUpperStarTensorNatIso

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
end WeilConjectures.PurityFiniteSetting
