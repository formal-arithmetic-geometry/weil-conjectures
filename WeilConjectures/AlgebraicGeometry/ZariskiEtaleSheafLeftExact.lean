/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Sheaf

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-!
# Left exactness of pullback from Zariski to étale sheaves

The sheaf pullback along a representably flat continuous functor from the opens of a scheme to
its small étale site preserves finite limits.

## References

* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
* [Stacks Project, Tag 00WJ](https://stacks.math.columbia.edu/tag/00WJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- Left exactness of the canonical sheaf pullback from the Zariski site to the small étale
site along a representably flat continuous functor `i`, with arbitrary coefficient universe. -/
theorem zariski_to_etale_sheaf_left_exact
    (X : Scheme.{u})
    (i : X.Opens ⥤ X.Etale)
    (hcont : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
    [RepresentablyFlat i] :
    PreservesFiniteLimits (i.sheafPullback (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) := by
  let := hcont
  let : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  let := preservesFiniteLimits_op_lan_of_flat
    (H := Type (max (u + 1) v)) i
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

end AlgebraicGeometry
