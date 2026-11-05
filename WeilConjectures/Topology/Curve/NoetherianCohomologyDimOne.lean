/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing

/-!
# Second cohomology on Noetherian spaces of dimension at most one

Source: Stacks Project, Cohomology, Proposition 02UZ, specialized to `d = 1` and `p = 2`
(blueprint: lem-sc-noetherian-cohomology-vanishing-abelian-dim-one).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

end TopCat.Sheaf
