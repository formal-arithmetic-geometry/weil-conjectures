/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateZeroBaseChange

/-! # Pullback of the supported coordinate product -/

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

/-- Arbitrary pullback preserves the actual supported coordinate product.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final Cartier-map base-change
sentence; parent proof Step 3 (blueprint: lem-pur-coordinate-supported-product-pullback).

Proof: each coordinate divisor pulls back to its namesake, and multiplication
by the corresponding polynomial variable remains injective over an arbitrary
coefficient ring, including after killing other coordinates. Apply the geometric
Cartier naturality clause of cartier_kummer_map to each actual boundary, at the
chosen annihilating exponent. Induct over the coordinate list defining product.
The empty step is the normalized constant unit; the successor uses the supported
cup pullback equation, exact monoidal inverse image, and its single and shift
comparisons. This is the tensor product target, so retain its ordered tensor
pullback comparison rather than replacing it by an arbitrary Tate isomorphism.
For the full list, the comparison of the pulled-back total intersection with
the primed zero section is unique over the affine space. Restriction of the
constant unit normalizes its coefficient exchange. Thus it agrees with
coordinateSourcePullback, and the ordered tensor target comparison agrees with
targetPullbackIso. Transport the list induction by these identifications.
The argument includes the empty list, an empty base and zero coefficients. -/
theorem coordinate_supported_product_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    (coordinateSourcePullback P n g c).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (supportedClass P n B aB c) ≫
        (targetPullbackIso P n (spaceMap g c) (towerBase aB c) c).hom =
      supportedClass P n B' (g ≫ aB) c := by sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
