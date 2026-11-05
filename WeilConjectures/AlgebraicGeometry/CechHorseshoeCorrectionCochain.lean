/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # A correction cochain from local horseshoe lifts

Source: Stacks Project, Cohomology, Tag 01EQ and Tag 0B8S.
(blueprint: lem-sc-cech-horseshoe-correction-cochain).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

end AlgebraicGeometry.Scheme.Modules
