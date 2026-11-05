/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

/-!
# Comparing module specialization with strict-local abelian specialization

Source: Stacks Project, Tags 0GJ2 and 0GKD, the geometric-germ construction.
(blueprint: lem-weil-pbc-module-specialization-abelian-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
