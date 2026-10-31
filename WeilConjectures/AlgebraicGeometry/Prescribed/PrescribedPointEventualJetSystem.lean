/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniSections
import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointInfinitesimalModel
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveTwistRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.DeligneLaumon.GeneratingSystemOpenTransport

/-!
# High-degree prescribed first-order linear systems

Source: Stacks Project, Tags 0FD5 and 0B5T, and the finite first-neighbourhood argument
in blueprint main-20261015, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-prescribed-point-eventual-jet-system).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] prescribedPointJet prescribedPointRestrictedFamily
  prescribedPointCombination prescribedPointVanishes tensorPullback Scheme.Modules.pullback

set_option maxHeartbeats 1500000 in
-- One construction combines the finite kernel basis, adjunction comparisons and jet lifts.
end

end AlgebraicGeometry
