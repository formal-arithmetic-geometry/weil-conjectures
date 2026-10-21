/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.CompactProductTwistLaws
public import Sheaf.Paper.SupportedExteriorClassArrows
public import Sheaf.Paper.SupportedClassGeometry
public import Sheaf.Paper.SupportedClassSiteComparison
public import Sheaf.Paper.SupportedExteriorShift
public import Sheaf.Paper.SupportedTwistMultiplication
public import Sheaf.Paper.SupportedTwistPullback
public import Sheaf.Paper.CompactProductProperSupportLaws
public import Sheaf.AlgebraicGeometry.ProperSupportCompactMaps
public import Sheaf.Paper.CompactProductRealizationLaws
public import Sheaf.AlgebraicGeometry.CompactProductRealizationArrows
public import Sheaf.Paper.CompactProductRealizationCoreLaws
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
import Sheaf.AlgebraicGeometry.SupportSiteComparison
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.SupportedCup
import Sheaf.Paper.SupportedCupFunctoriality
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
