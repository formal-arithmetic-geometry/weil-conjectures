/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateProductComparison
import WeilConjectures.AlgebraicGeometry.CoordinateProductConsSupportData
import WeilConjectures.AlgebraicGeometry.CoordinateProductConsEquation

/-! # Extending a support-product comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and even shifts
(blueprint: lem-pur-coordinate-product-cons-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

/-- Extending a support-product comparison.
Source: supported coordinate products in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-product-cons-compatibility).

Proof: the successor support isomorphism over the affine tower and the successor
length equality are the base change of the given support isomorphism along the
divisor inclusion of `i` (coordinate_product_cons_support_data). The product equation
for any such isomorphism is coordinate_product_cons_equation. -/
theorem coordinate_product_cons_compatibility (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c)
    {is js : List (Fin c)} (h : CoordinateProductsAgree P n B aB c is js) :
    CoordinateProductsAgree P n B aB c (i :: is) (i :: js) := by
  obtain ⟨e, he, hlen⟩ := coordinate_product_cons_support_data P n B aB c i h
  exact ⟨e, he, hlen, coordinate_product_cons_equation P n B aB c i h e he hlen⟩

end AlgebraicGeometry.ProEtale.AffineZeroPurity
