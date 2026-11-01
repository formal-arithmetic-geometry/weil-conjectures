/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CoefficientFirstCompactSupportSiteSquarePasting

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
end AlgebraicGeometry.ProEtale.VectorIntegrationSite
