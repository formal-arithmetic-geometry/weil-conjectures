/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Open restriction compatibility of the tensor pullback unit

Source: Stacks Project, Tags 0096 and 0098.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry

section

-- These APIs keep open-immersion constructions abstract during elaboration.

end

-- The germ argument uses arbitrary sheaves, so tensor constructions remain abstract.

end AlgebraicGeometry
