/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext

public import WeilConjectures.Topology.OpenModuleCohomology
import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Natural comparison of restriction cohomology and open derived sections

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-open-restriction-module-cohomology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] openComparison_enoughInjectives

noncomputable section

end

end AlgebraicGeometry
