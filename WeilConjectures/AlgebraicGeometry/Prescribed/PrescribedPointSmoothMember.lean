/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointBertiniOpen
import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Bertini for a linear system with finite prescribed base locus

Source: Stacks Project, Tag 0FD6, and blueprint main-20261015,
finite-cover-curve proof, paragraph 2, first derivative conditions.
(blueprint: lem-zl-prescribed-point-smooth-member).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local instance] cachedSheafify cachedWEquals

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

attribute [local irreducible] tensorPullback tensorPullbackObj
  prescribedPointJet prescribedPointRestrictedFamily prescribedPointCombination
  prescribedPointMember prescribedPointVanishes

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end

end AlgebraicGeometry
