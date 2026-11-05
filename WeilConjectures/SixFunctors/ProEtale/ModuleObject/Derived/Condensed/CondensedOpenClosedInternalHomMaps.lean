/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction

/-!
# Open and closed formulas for internal derived Hom

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.13, internal
adjunction calculation; Stacks Project Tag 08JB
(blueprint: def-sfb-open-closed-internal-hom-comparisons).

All categories are ordinary unbounded derived categories of modules over the pulled-back
commutative condensed coefficient ring. Support inverse image is canonically identified
with the recorded upper star by `supportPullbackIsoUpperStar`. No completion or finiteness
condition on a derived input is imposed. The closed termwise constructions take the
exactness of direct image explicitly. For a complementary quasi-compact open immersion,
`closedSupport_lowerStarExact` supplies this instance. The comparison maps are constructed
by projection and evaluation transposes; invertibility and naturality are separate results.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
