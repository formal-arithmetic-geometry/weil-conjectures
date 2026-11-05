/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTower
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Normalized towers of perfect complexes over the quotients of a complete local ring

Let `R` be a local ring, complete for an ideal `I = (ϖ)` contained in its maximal ideal (the
intended case being `R = 𝒪_E` and `I = 𝔪_E`). This file specializes the results of
`WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTower` to normalized towers of perfect
complexes over the tower of local rings `n ↦ R ⧸ Iⁿ⁺¹`: the derived limit of such a tower is
represented by a bounded complex of finite free `R`-modules and reduces to the levels, compatible
families of endomorphisms lift to the derived limit, and the trace of a lift is the limit of the
levelwise traces.

## Main definitions

- `Ideal.powSuccMk I n : R →+* R ⧸ Iⁿ⁺¹` and `Ideal.powSuccFactor I n : R ⧸ Iⁿ⁺² →+* R ⧸ Iⁿ⁺¹`:
  the tower of quotients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

variable {I}

end Ideal

namespace ModuleCat.NormalizedPerfectTower

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} [IsLocalRing R] [IsAdicComplete I R]
  {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (hI : I = Ideal.span {ϖ})
  (T : NormalizedPerfectTower I.powSuccMk I.powSuccFactor I.powSuccMk_eq)
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

section Trace

/-! The braiding of the derived categories is the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product. The trace statements below
hold for every choice of right duals; both are available by perfectness
(`ModuleCat.NormalizedPerfectTower.hasRightDualPt`,
`ModuleCat.NormalizedPerfectTower.hasRightDualObj`). -/

attribute [local instance] DerivedCategory.braidedCategory'

variable [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

end Trace

end ModuleCat.NormalizedPerfectTower
