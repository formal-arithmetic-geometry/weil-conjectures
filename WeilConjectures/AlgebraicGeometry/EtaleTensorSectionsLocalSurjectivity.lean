/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsOpenLift
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Local lifting of tensor sections of an epimorphism

Source: Stacks Project, Tags 070S(2), 03FH(1), and 0096.
(blueprint: lem-sc-etale-tensor-sections-local-surjectivity)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

end
end AlgebraicGeometry.Scheme.Modules
