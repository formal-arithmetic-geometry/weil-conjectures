/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionArrows
import WeilConjectures.AlgebraicGeometry.CoordinateSupportedProductZero
import WeilConjectures.AlgebraicGeometry.CoordinateSupportedProductSuccessor

/-! # Supported coordinate product versus proper projection

Source: cor-pur-affine-space-zero-section-purity, ordered Cartier-product paragraph.
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

/-- The compactly supported coordinate product has the empty-product normalization
and the successor formula obtained from the proper projection map.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product and
projection-formula sentence; parent proof Steps 1--5
(blueprint: lem-pur-coordinate-supported-product-recursion).

Proof: Work first in ordinary etale degree-zero flat models for closed constants.
Coordinates remain nonzerodivisors after adjoining or killing other coordinates,
so Cartier naturality identifies the first r factors on X_(r+1) with pullback of
C_r. Their intersection with the last section is exactly the full zero section.
The supported cup is inverse coefficient multiplication followed by the tensor
of these maps and normalized Tate multiplication. The counit-defined projection
map at the supported coefficient object is the same coefficient multiplication,
after symmetry: both restrict sections to the intersection and multiply them.
Naturality of projection for C_r therefore replaces this tensor cup by s_* C_r
followed by the inverse projection at W_r and the last Cartier factor. This is
sectionArrow by its defining projection equation. The finite projection formula
applies to W_r because finite Tate lines are locally free of rank one. Exact
monoidal site comparison transports this equality to the specified pro-etale
arrows. Unique support transport and the fixed proper closed comparison give
coordinateComposition. Every reordered shift is even, so its sign is one. At
rank zero the empty intersection and coefficient multiplication are identities;
the proper closed comparison is the normalized compact-support identity. The
inverse exceptional Hom bijection in compactProduct cancels the bijection used
in thom, so it recovers this same supported map. This argument includes an empty
base and uses no relative supported Kunneth assertion. -/
theorem coordinate_supported_product_recursion (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    compactProduct P n B aB 0 = coordinateIdentity P n B ∧
    (∀ r : ℕ, compactProduct P n B aB (r + 1) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map (compactProduct P n B aB r) ≫ sectionArrow P n B aB r) := by
  constructor
  · exact coordinate_supported_product_zero P n B aB
  · intro r
    exact coordinate_supported_product_successor P n B aB r

end AlgebraicGeometry.ProEtale.AffineZeroPurity
