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

## References

* Stacks Project, Tag 02UZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

/-- The second cohomology of every abelian sheaf on a Noetherian topological space of
Krull dimension at most one is zero. -/
theorem isZero_secondCohomology_of_noetherian_dim_le_one
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (CategoryTheory.Sheaf.H' F 2 (⊤ : Opens X)) := by
  exact TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound
    X 1 hdim F 2 (by decide)

end TopCat.Sheaf
