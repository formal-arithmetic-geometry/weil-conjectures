/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
import all WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Composition for the fixed-coefficient derived site comparison

Source: blueprint lem-weil-pbc-comparison-pullback, composition clause.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.Dnc

private theorem reverse_square {C : Type*} [Category C]
    {O O₁ O₂ O₃ O₄ : C} (e : O ≅ O₁) (a : O₁ ≅ O₂) (b : O₂ ≅ O₃)
    (c : O ≅ O₄) (d : O₄ ≅ O₃) (h : e ≪≫ a ≪≫ b = c ≪≫ d) :
    c.symm ≪≫ e = d ≪≫ b.symm ≪≫ a.symm := by
  have hh := congrArg (fun z ↦ c.symm ≪≫ z ≪≫ b.symm ≪≫ a.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
    Iso.refl_trans, Iso.trans_refl, Iso.self_symm_id] using hh

private theorem etale_comp_hom (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (K : _root_.DerivedCategory (Sheaf R.smallEtaleTopology C)) :
    (Etale.leftDerivedUpperStarComp C a b).hom.app K =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory C (a ≫ b)).hom.app K ≫
        (Functor.mapDerivedCategoryTriangleIso (Etale.upperStarComp C a b)).hom.app K ≫
        (Etale.upperStar C a).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C b).inv.app K) ≫
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory C a).inv.app
          ((Etale.upperStar C b).leftDerivedFunctor.obj K) := by
  simp only [Etale.leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The specified derived comparison respects composition of scheme inverse images.
Proof: apply exact-functor derivation to the ordinary comparison's composition law,
then conjugate the derived exact inverse images to the specified left derived functors.
Naturality cancels the two intermediate conjugating isomorphisms.
Source: blueprint lem-weil-pbc-comparison-pullback, composition clause.

(blueprint: lem-pur-comparison-pullback-derived-coherence).
-/
theorem pullComparison_comp (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (K : _root_.DerivedCategory (Sheaf R.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    (pullComparison P (a ≫ b) K).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).hom.app K) =
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).hom.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) R).mapDerivedCategory.obj K) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
          (pullComparison P b K).hom ≫
        (pullComparison P a
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K)).hom :=
  by
  let C := ModuleCat.{u + 1} P.Coefficient
  have h : ∀ M : Sheaf R.smallEtaleTopology C,
      (ProEtale.comparisonUpperStarCompUpperStarIso C (a ≫ b)).hom.app M ≫
          (ProEtale.comparisonUpperStar C T).map ((Etale.upperStarComp C a b).hom.app M) =
        (ProEtale.upperStarComp C a b).hom.app
            ((ProEtale.comparisonUpperStar C R).obj M) ≫
          (ProEtale.upperStar C a).map
            ((ProEtale.comparisonUpperStarCompUpperStarIso C b).hom.app M) ≫
          (ProEtale.comparisonUpperStarCompUpperStarIso C a).hom.app
            ((Etale.upperStar C b).obj M) := by
    intro M
    have hc := ProEtale.comparison_comp C a b M
    have hi :
        (ProEtale.comparisonUpperStar C T).mapIso ((Etale.upperStarComp C a b).app M) ≪≫
          (ProEtale.comparisonUpperStarCompUpperStarIso C a).symm.app
            ((Etale.upperStar C b).obj M) ≪≫
          (ProEtale.upperStar C a).mapIso
            ((ProEtale.comparisonUpperStarCompUpperStarIso C b).symm.app M) =
        (ProEtale.comparisonUpperStarCompUpperStarIso C (a ≫ b)).symm.app M ≪≫
          (ProEtale.upperStarComp C a b).app
            ((ProEtale.comparisonUpperStar C R).obj M) := by
      apply Iso.ext
      exact hc
    have hh := reverse_square _ _ _ _ _ hi
    exact congrArg Iso.hom hh
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (ProEtale.comparisonUpperStarCompUpperStarIso C b)
    (ProEtale.comparisonUpperStarCompUpperStarIso C a)
    (ProEtale.comparisonUpperStarCompUpperStarIso C (a ≫ b))
    (ProEtale.upperStarComp C a b) (Etale.upperStarComp C a b) h K
  have hnat :=
    (Functor.mapDerivedCategorySquareIso
      (ProEtale.comparisonUpperStarCompUpperStarIso C a)).hom.naturality
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory C b).inv.app K)
  simp only [Functor.comp_map] at hnat
  rw [ProEtale.leftDerivedUpperStarComp_hom_app, etale_comp_hom]
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  erw [NatIso.naturality_1_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hnat, reassoc_of% H]
  rfl

/-- The fixed site comparison commutes with maps, including inverse orientations.
Source: naturality of the derived comparison-pullback isomorphism.
(blueprint: lem-pur-comparison-pullback-derived-coherence).
-/
theorem pullComparison_naturality (P : PurityFiniteSetting.{u}) {B B' : Scheme.{u}}
    (b : B' ⟶ B) {K L : Etale.DerivedCategoryModule P.Coefficient B} (e : K ≅ L) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso e) ≪≫
        pullComparison P b L =
      pullComparison P b K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
            ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso e) :=
  by
  let η := Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) b) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) b ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) b).symm
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory
  apply Iso.ext
  exact η.hom.naturality e.hom

end WeilConjectures.PurityFiniteSetting.Dnc
