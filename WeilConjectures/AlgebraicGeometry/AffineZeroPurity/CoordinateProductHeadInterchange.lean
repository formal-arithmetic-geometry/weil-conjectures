/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductsAgree.CoordinateProductComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductHeadSupportIso
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductHeadProductEquation

/-! # Exchanging the two outermost cup factors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: lem-pur-coordinate-product-head-interchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory DerivedCategory.braidedCategory'
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

/-- Exchanging the two outermost cup factors.
Source: supported coordinate products in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-product-head-interchange).

Proof: expand the two successor products, leaving the tail product unchanged.
Associativity of supported coefficient multiplication identifies the two triple
intersections. In the common tensor parenthesization, naturality carries the
two boundary arrows past the source braiding. The proved coefficient support
symmetry changes their order at coefficient level. The target map is the associator followed
by identity tensor the self-braiding of the shifted line and the inverse
associator. The supplied identity cancels that map. This produces the support
isomorphism over the affine tower, the reflexive length equality, and the
required equation before any full-intersection normalization. -/
theorem coordinate_product_head_interchange (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i j : Fin c) (is : List (Fin c))
    (hbraid : (β_ (shiftedLine (setting P n) (iteratedAffineLine B c))
      (shiftedLine (setting P n) (iteratedAffineLine B c))).hom = 𝟙 _) :
    CoordinateProductsAgree P n B aB c (i :: j :: is) (j :: i :: is) := by
  obtain ⟨e, he⟩ := coordinate_product_head_support_iso P n B c i j is
  refine ⟨e, he, rfl, ?_⟩
  simpa only [eqToHom_refl, Category.comp_id] using
    (coordinate_product_head_product_equation P n B aB c i j is e he hbraid)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
