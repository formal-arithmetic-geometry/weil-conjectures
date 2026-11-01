/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import Mathlib.CategoryTheory.Iso
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CoefficientFirstCompactSupportSiteSquareSpecializedSquare

/-! # Coefficient-first compact-support projection square
Source: Stacks 099R, 0944, 0GL1; the proper/open site comparison square.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

private theorem composite_iso_square
    {C : Type*} [Category C] {X Y Z T U : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : T ≅ U) :
    c.hom ≫ d.hom ≫ (a ≪≫ b ≪≫ c ≪≫ d).inv = b.inv ≫ a.inv := by
  simp only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
