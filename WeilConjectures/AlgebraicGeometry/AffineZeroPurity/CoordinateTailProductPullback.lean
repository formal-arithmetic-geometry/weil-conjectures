/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorSupport
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorSupport
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryPullback
import all Mathlib.Logic.Small.Defs

/-! # Pulling back the old factors in a successor coordinate product

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

-- Use the same cached ordinary Ext instances as the normalized Cartier family.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private theorem transport_normalized {C : Type*} [Category C]
    {W X Y Z : C} (f : W ⟶ X) (h : X = Y) (k : Y = Z) :
    (f ≫ eqToHom h) ≫ eqToHom k = f ≫ eqToHom (h.trans k) := by
  subst Y
  subst Z
  simp only [eqToHom_refl, Category.comp_id]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
