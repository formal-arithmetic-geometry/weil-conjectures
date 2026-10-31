/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.CoefficientFirstCompactSupportSiteSquarePasting

/-! # The compact-support projection comparison in coefficient-first coordinates. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

-- Elaborate using the standard structures named by the Cartier aliases.
attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem compared_projection_formula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    comparedModuleProjection A c W K =
      projection (ModuleCat.{u + 1} A) c
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (tensorPullbackComparison A f K W).inv := by
  unfold comparedModuleProjection moduleProjection
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem projection_formula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    projection (ModuleCat.{u + 1} A) c
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K) =
      ((symmetry (ModuleCat.{u + 1} A) Y).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K)).app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)) ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((symmetry (ModuleCat.{u + 1} A) X).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).app
            ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
              ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))) := by
  unfold projection
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
/-- The coefficient-first compact-support comparison square in comparison-source
coordinates. Source: Stacks Tags 0944 and 0GL1 for the compactified projection,
Tag 099R for comparison, with the canonical monoidal comparison of Tag 07A4.
(blueprint: lem-route-coefficient-first-compact-support-site-square-coefficient).

Proof: use coefficientFirstCompactSupportPasting. The right side of that equation
is the tensor comparison, tensor of inverse comparison at W, and the actual
coefficient-first pro-etale projection. Postcompose with compact support of the
inverse tensor/pullback comparison. Its hom and inv cancel by functoriality.
The resulting pro-etale projection is precisely comparedModuleProjection by its
definition. Combine the three images on the ordinary side using map_comp. This
gives the claimed equation. No projection-formula invertibility is assumed.
-/
theorem coefficientFirstCompactSupportCoefficientSquare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W)
    (hM : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj K)).obj W)) :
    let Le := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let TY := derivedTensor (ModuleCat.{u + 1} A) Y
    let VY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let b := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
      ((Etale.ordinaryFinitePullback A f).obj K)
    let bY := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app (Le.obj W)
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K).hom.app (Le.obj W) ≫
      (TY.obj (VY.obj K)).map ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩) ≫
      comparedModuleProjection A c W K =
    VY.map (bY ≫ ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app W).app K ≫
      Le.map b) ≫ (compactSupportSiteComparison A c).inv.app ⟨_, hM⟩ := by
  let Lp := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  have h := coefficientFirstCompactSupportPasting A f c W K hW hM
  have hτ : Lp.map (tensorPullbackComparison A f K W).hom ≫
      Lp.map (tensorPullbackComparison A f K W).inv = 𝟙 _ := by
    exact (Lp.mapIso (tensorPullbackComparison A f K W)).hom_inv_id
  have hc := congrArg
    (fun z => z ≫ Lp.map (tensorPullbackComparison A f K W).inv) h
  dsimp only [Lp, comparison, geoP1Comparison, Functor.comp_obj,
    Functor.flip_obj_obj, ObjectProperty.ι_obj,
    Etale.derivedTensorRightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.id_obj] at hτ hc ⊢
  simp only [Category.assoc] at hc
  erw [hτ] at hc
  simpa only [compared_projection_formula, projection_formula, Functor.map_comp,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj,
    Category.assoc, Category.comp_id] using hc.symm

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
