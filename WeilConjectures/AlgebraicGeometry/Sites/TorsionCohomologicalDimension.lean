/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsion étale cohomological dimension

A scheme `X` has torsion étale cohomological dimension at most `c`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE X c`) if `Hᵠ(X_ét, F) = 0` for
every torsion abelian étale sheaf `F` on `X` and every `q > c`. For a field `K` this is the
condition `cd_tor(K) ≤ c` on `Spec K`.

The torsion étale cohomological dimension `cd(X) ∈ ℕ∞` of blueprint `def-kun-cd` is
`AlgebraicGeometry.Scheme.torsionCohomologicalDimension`, the least such `c` (or `⊤`); its
relative version for a morphism `f`, defined by the vanishing of the higher direct images
`Rᵠf_* F` of torsion sheaves, is `AlgebraicGeometry.Scheme.Hom.torsionCohomologicalDimension`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Blueprint `def-sc-etale-torsion-cd`: Etale torsion cohomological dimension bound.

`cd_tor(X) ≤ c`: the étale cohomology `Hᵠ(X_ét, F)` vanishes for every torsion abelian étale
sheaf `F` on `X` and every `q > c`. -/
def HasTorsionCohomologicalDimensionLE (X : Scheme.{u}) (c : ℕ) : Prop :=
  ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
    ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q)

lemma HasTorsionCohomologicalDimensionLE.mono {X : Scheme.{u}} {c d : ℕ}
    (h : X.HasTorsionCohomologicalDimensionLE c) (hcd : c ≤ d) :
    X.HasTorsionCohomologicalDimensionLE d :=
  fun F hF q hq ↦ h F hF q (lt_of_le_of_lt hcd hq)

end AlgebraicGeometry.Scheme
