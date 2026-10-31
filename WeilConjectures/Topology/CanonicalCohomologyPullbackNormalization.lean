/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Topology.CanonicalCohomologyPullback
/-! # Normalization of the canonical topological cohomology pullback
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB.
(blueprint: lem-weil-pbc-canonical-topological-pullback-normalization)
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace TopCat
/-- The canonical family satisfies its specifying naturality, boundary and unit laws.
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB.
(blueprint: lem-weil-pbc-canonical-topological-pullback-normalization)

Proof: Unfold objectCohomologyPullback once. Its definition is Classical.choose applied
to siteCohomology_pullback_exists. Classical.choose_spec of that same existence theorem
is exactly IsPullback for the chosen family. The topological inverse-image additivity
instance is sheafPullbackAb_additive, and the continuous inverse-image functor supplies
finite-limit and finite-colimit preservation. No new geometric assertion is required. -/
theorem objectCohomologyPullback_normalized {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SiteCohomologyFamily.IsPullback (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f) (objectCohomologyPullback f) := by
  unfold objectCohomologyPullback
  exact Classical.choose_spec (siteCohomology_pullback_exists
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) (Opens.map f))
end TopCat
