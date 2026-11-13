/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.PullbackIsoNsmulDevissage
import WeilConjectures.AlgebraicGeometry.PullbackIsoTorsionColimit

/-!
# Pullback isomorphisms on cohomology: prime-torsion dévissage

## References

* Stacks Project, Tag 0A4B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If pullback is bijective on every prime-torsion étale abelian sheaf, then it is
bijective on every torsion étale abelian sheaf (Stacks, Tag 0A4B). -/
theorem pullback_cohomology_bijective_of_prime_torsion_devissage
    {X Y : Scheme.{u}} (u : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (hprime : ∀ (r : ℕ), Nat.Prime r →
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        r • 𝟙 G = 0 → ∀ (q : ℕ),
          Function.Bijective (cohomologyMap u G q))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    ∀ (q : ℕ), Function.Bijective (cohomologyMap u F q) := by
  apply pullback_cohomology_bijective_of_torsion_colimit u
  · intro n hn G hG q
    exact pullback_cohomology_bijective_of_nsmul u hprime hn G hG q
  · exact hF

end AlgebraicGeometry.Etale
