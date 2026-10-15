/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Sheaf.CategoryTheory.SiteCohomologyPullbackExists
public import Sheaf.CategoryTheory.SiteCohomologyPullbackUnique

/-! # Canonical pullback on topological object cohomology

Source: Stacks Project, Cohomology, Tags 01F8 and 01FB.
(blueprint: def-weil-pbc-topological-object-cohomology-pullback)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Functor.sheafPullbackConstruction

namespace TopCat

/-- The constructed inverse image is left adjoint to continuous direct image.
Source: Stacks Project, Sheaves, Tag 008C.
(blueprint: def-weil-pbc-topological-object-cohomology-pullback) -/
instance sheafPullbackAb_isLeftAdjoint {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (sheafPullback (Opens.map f) AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsLeftAdjoint :=
  (sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint

/-- Additivity of topological abelian inverse image, from its finite-limit preservation.
Source: Stacks Project, Sheaves, Section 008C; Mathlib,
`Functor.additive_of_preserves_binary_products`.
(blueprint: def-weil-pbc-topological-object-cohomology-pullback) -/
instance sheafPullbackAb_additive {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (sheafPullback (Opens.map f) AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The unique unit-normalized, natural, boundary-compatible pullback on object cohomology.
Source: Stacks Project, Cohomology, Tags 01F8 and 01FB.
(blueprint: def-weil-pbc-topological-object-cohomology-pullback)

The existence theorem specifies the normalization property `IsPullback`;
`siteCohomology_pullback_unique` proves that this property determines the entire family.
Thus the choice here is uniquely determined, rather than arbitrary cohomology data. -/
def objectCohomologyPullback {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f) :=
  Classical.choose (siteCohomology_pullback_exists
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) (Opens.map f))

end TopCat
