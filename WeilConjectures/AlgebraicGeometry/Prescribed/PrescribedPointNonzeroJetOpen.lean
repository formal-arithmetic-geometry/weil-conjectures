/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData

import WeilConjectures.Mathlib.Topology.Sober
import Mathlib.RingTheory.KrullDimension.Field

/-!
# An open condition of nonzero prescribed jets

Source: blueprint, finite-cover-curve proof, paragraph 2, derivative conditions.
(blueprint: lem-zl-prescribed-point-nonzero-jet-open).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end

end AlgebraicGeometry
