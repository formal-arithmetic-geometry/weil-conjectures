/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen

/-!
# Cohomology of sheaves supported in low dimension

Let `B` be an affine scheme of finite type over a field `K` and `N` a torsion abelian étale
sheaf on `B` whose geometric stalks vanish at every point `y` with `trdeg_K κ(y) > a`. If every
closed subscheme `Z` of `B` of dimension at most `a` satisfies `cd_tor(Z) ≤ a`, then
`Hᵖ(B, N) = 0` for `p > a`
(`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg`).

Indeed `N` is the directed union of its subsheaves `N_Z` of sections supported in closed subsets
`Z` of dimension at most `a` (`AlgebraicGeometry.Etale.exists_covering_supportedIn`, blueprint
`lem-sc-support-dimension-union`), étale cohomology of the quasi-compact quasi-separated `B`
commutes with directed unions (`AlgebraicGeometry.Scheme.H_map_of_directed_of_locally`), and
`N_Z = i_* i^* N_Z` for the closed immersion `i` of the reduced closed subscheme on `Z`, whose
cohomology is that of `i^* N_Z` on `Z` (`AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Cohomology of a sheaf supported in low dimension.** Let `B` be an affine scheme of finite
type over a field `K` (structure morphism `b`), `a ≥ 0`, and suppose that every closed
subscheme of `B` of dimension at most `a` has torsion cohomological dimension at most `a`. Let
`N` be a torsion abelian étale sheaf on `B` whose geometric stalks vanish at every point `y`
with `trdeg_K κ(y) > a`. Then `Hᵖ(B, N) = 0` for every `p > a`. -/
theorem subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg {K : Type u} [Field K]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsAffine B] (a : ℕ)
    (hZ : ∀ (Z : Scheme.{u}) (i : Z ⟶ B), IsClosedImmersion i →
      topologicalKrullDim Z ≤ (a : WithBot ℕ∞) → Z.HasTorsionCohomologicalDimensionLE a)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N))
    (p : ℕ) (hp : a < p) : Subsingleton (Sheaf.H N p) :=
  sorry

end AlgebraicGeometry.Etale
