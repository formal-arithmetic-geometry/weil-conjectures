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

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- For a continuous, representably flat functor `i` from Zariski opens to the small étale
site, the sheaf pullback along `i` preserves finite limits, with coefficients in an arbitrary
universe. Stacks Project, Tag 00X5 (using Tags 00X3 and 00WJ). -/
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
