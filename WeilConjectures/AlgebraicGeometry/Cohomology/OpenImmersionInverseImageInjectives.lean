/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackInjectives
/-! # Open inverse image preserves injectives

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- Inverse image along an open immersion preserves injective abelian sheaves.
Source: Stacks Project, Tags 03DI and 03DJ. -/
theorem invImage_preservesInjectiveObjects_of_openImmersion {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] : (invImage j).PreservesInjectiveObjects := by
  change (TopCat.Sheaf.pullback AddCommGrpCat.{u} j.base).PreservesInjectiveObjects
  exact Topology.isOpenEmbedding_sheafPullback_preservesInjectiveObjects
    j.base j.isOpenEmbedding

end AlgebraicGeometry.Scheme.Modules
