/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCohomologyStageContinuity
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Two-open gluing of continuity

Source: Stacks Project, Tags 09YQ (theorem-colimit) and 0A50 (lemma-mayer-vietoris).
(blueprint: lem-weil-pbc-etale-limit-cohomology-binary-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Continuity glues across a union of two quasi-compact opens.

Source: Stacks Project, Tags 09YQ (theorem-colimit) and 0A50 (lemma-mayer-vietoris);
step 2 of lem-weil-pbc-etale-limit-cohomology-qcqs-gluing.
(blueprint: lem-weil-pbc-etale-limit-cohomology-binary-gluing).

Proof:
1. For a system with a stage isomorphic to U union V, pass to the cofinal tail
   above that stage and transport U and V through the specified isomorphism.
   Restrict the scheme cone and every stage sheaf to inverse images of the opens.
   The restricted scheme cones are limits and the maps remain affine. The opens
   are quasi-compact, and quasi-separatedness is inherited from the stage.
   Inverse image preserves the supplied sheaf colimit. Inverse-image composition
   and cohomology pullback functoriality identify all comparison legs. Apply the
   three hypotheses to these restricted systems, in all degrees.
2. Mayer-Vietoris and its naturality in sheaves and scheme pullback supply a map
   between the colimit of the stage exact sequences and the sequence on the limit.
   Filtered abelian-group colimits preserve exactness and finite products. For
   positive p use the segment H^(p-1)(U)+H^(p-1)(V), H^(p-1)(U intersection V),
   H^p(U union V), H^p(U)+H^p(V), H^p(U intersection V). The four outer comparison
   maps are isomorphisms by the hypotheses, so the five lemma gives the middle one.
   In degree zero use the initial zero terms; no negative cohomology is invoked.
3. Transport the colimit universal property along the resulting isomorphism and
   the supplied eB. Naturality makes its legs precisely hB. Reflect the resulting
   colimit back along the final tail inclusion.

Edge cases: empty U or V give the identity comparison on the other open. Both
empty give zero groups. U=V uses the diagonal and difference maps. No separatedness
of the ambient scheme is required; the stages of each quantified system are qcqs.
-/
theorem etale_limit_cohomology_binary_gluing
    (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hCU : EtaleCohomologyStageContinuity U.toScheme)
    (hCV : EtaleCohomologyStageContinuity V.toScheme)
    (hCI : EtaleCohomologyStageContinuity (U ⊓ V).toScheme) :
    EtaleCohomologyStageContinuity (U ⊔ V).toScheme := by sorry

end AlgebraicGeometry.Etale
