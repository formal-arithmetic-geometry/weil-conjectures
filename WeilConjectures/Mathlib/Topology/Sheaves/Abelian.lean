/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

/-!
# Exactness of the pullback of abelian sheaves on a topological space

The pullback of sheaves of abelian groups along a continuous map of topological spaces is
exact: it preserves finite colimits because it is a left adjoint (this is
`CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`), and it preserves finite
limits because `TopologicalSpace.Opens.map f` is representably flat
(`TopologicalSpace.Opens.preservesFiniteLimits_sheafPullback`).

Mathlib proves the latter for an arbitrary concrete coefficient category over small sites,
but that instance is not found in practice: the metavariables for the concreteness data
make the instance search diverge. This file records the specialisation to `AddCommGrpCat`
over the sites of open subsets of topological spaces, which is what is needed for sheaf
cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

set_option maxHeartbeats 1000000 in
-- Elaborating the underlying left Kan extension is expensive; see the module docstring.
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- The pullback of sheaves of abelian groups along a continuous map is left exact. -/
instance preservesFiniteLimits_sheafPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

end TopologicalSpace.Opens
