/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Torsion cohomological dimension of a finite-type scheme

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
thm-sc-finite-type-torsion-cd.md (blueprint: thm-sc-finite-type-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite-type scheme of dimension `d` over a field of torsion étale cohomological
 dimension at most `c` has torsion étale cohomological dimension at most `2 * d + c`.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-finite-type-torsion-cd.md
(blueprint: thm-sc-finite-type-torsion-cd).

Proof: Apply the affine-to-global Leray reduction
`new-thm-sc-finite-type-torsion-cd-affine-reduction`, supplying the affine finite-type
calculation `new-thm-sc-affine-torsion-cd-bound`. The comparison from the étale to the
Zariski site has exact inverse image, so gives a Leray spectral sequence. Its higher
direct-image stalks are filtered colimits of cohomology on affine neighborhoods and
vanish above `d + c` by the affine calculation. Zariski cohomology vanishes above `d`.
Thus all surviving total degrees are at most `2 * d + c`, for every locally torsion
abelian étale sheaf, with ordinary derived-section cohomology throughout. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_finiteType
    (K : Type u) [Field K] (c d : ℕ)
    (hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c)
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (hX : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    HasTorsionEtaleCohomologicalDimensionLE X (2 * d + c) := by
  sorry

end AlgebraicGeometry.Scheme

end
