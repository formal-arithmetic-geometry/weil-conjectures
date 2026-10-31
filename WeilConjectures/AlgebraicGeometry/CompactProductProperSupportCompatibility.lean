/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactProductTwistLaws
public import WeilConjectures.AlgebraicGeometry.SupportedExteriorClassArrows
public import WeilConjectures.AlgebraicGeometry.SupportedClassGeometry
public import WeilConjectures.AlgebraicGeometry.SupportedClassSiteComparison
public import WeilConjectures.AlgebraicGeometry.SupportedExteriorShift
public import WeilConjectures.AlgebraicGeometry.SupportedTwistMultiplication
public import WeilConjectures.AlgebraicGeometry.SupportedTwistPullback
public import WeilConjectures.AlgebraicGeometry.CompactProductProperSupportLaws
public import WeilConjectures.AlgebraicGeometry.ProperSupportCompactMaps
public import WeilConjectures.AlgebraicGeometry.CompactProductRealizationLaws
public import WeilConjectures.AlgebraicGeometry.CompactProductRealizationArrows
public import WeilConjectures.AlgebraicGeometry.CompactProductRealizationCoreLaws
import WeilConjectures.AlgebraicGeometry.ClosedSupportHom
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryKunnethFiniteRing
import WeilConjectures.AlgebraicGeometry.SupportSiteComparison
import WeilConjectures.AlgebraicGeometry.SupportedExteriorProduct
import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.SupportedCup
import WeilConjectures.AlgebraicGeometry.SupportedCupFunctoriality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Compact exterior products and proper-support compatibility

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: lem-pur-compact-product-proper-support-compatibility).

-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurityFiniteSetting

/-- Compact exterior products and properly supported classes, including excision,
signed finite twists and the specified finite etale-to-pro-etale comparisons.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: lem-pur-compact-product-proper-support-compatibility).

Proof: choose proper compactifications by compactification refinement. Apply the finite-ring
ordinary Kunneth theorem to the two zero extensions; their tensor is the zero extension of
the exterior product, by the open restriction and zero stalks off that open. This identifies
the named compact arrow and proves invertibility and naturality.
For proper closed supports, their maps into the compactifications are proper immersions,
hence closed. The constant-section units and the three support-adjunction counits identify
the two composites of the proper-support square with the same adjoint exterior morphism;
taking shifted Hom gives the formula on every supported class.
Excision restricts the support cone to the open neighbourhood of the closed support.
The open-adjunction mate into any specified bounded-below extension then identifies the
composite through compact support with inverse excision followed by forgetting support.
For signed twists, tensor the two supported representatives, apply the canonical shift
comparison and twist multiplication, and identify this with the pulled-back supported cup.
The support-site and compact-support-site comparison squares transport these same arrows
to each retained etale-origin witness and give the stated independence and normalization.
-/
theorem compactProductProperSupportCompatibility (P : PurityFiniteSetting.{u}) :
    P.CompactProductProperSupportLaws ∧ P.CompactProductTwistLaws ∧
      P.CompactProductRealizationLaws := by
  sorry

end WeilConjectures.PurityFiniteSetting
