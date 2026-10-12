/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# The proper direct image preserves coproducts

For a proper morphism `g : Z ⟶ Y` and finite (hence torsion) coefficients `Λ`, the total right
derived pushforward `Rg_*` on the unbounded derived categories of étale sheaves of `Λ`-modules
preserves arbitrary coproducts (blueprint `lem-amb-proper-coproducts`).

This is stated here without proof: it rests on the finite cohomological dimension of the proper
direct image for torsion coefficients (blueprint `thm-sc-finite-type-torsion-cd`) and on the
commutation of the higher direct images `Rᵃg_*` of a quasi-compact quasi-separated morphism
with filtered colimits, neither of which is formalised yet.

## Main statements

- `AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- Blueprint `lem-amb-proper-coproducts`: for a proper morphism `g : Z ⟶ Y` and finite
coefficients `Λ`, the total right derived pushforward `Rg_*` on the unbounded derived
categories of étale sheaves of `Λ`-modules preserves arbitrary (`u + 1`-small) coproducts.

The blueprint states this for a proper morphism of finite type between Noetherian schemes;
the Noetherian hypothesis is not used here. It is not needed: a proper morphism is
quasi-compact, quasi-separated and of finite type, so its geometric fibres have bounded
dimension `e` and, for torsion coefficients, `Rᵃg_* F = 0` for `a > 2e` and every sheaf `F`
(proper base change and the cohomological dimension of proper schemes over separably closed
fields); the higher direct images of the qcqs `g` commute with filtered colimits, hence with
direct sums. The finite amplitude then makes each cohomology sheaf `Hᵠ(Rg_* K)` depend only on
a bounded truncation of `K`, which reduces the coproduct comparison for unbounded complexes to
bounded ones. -/
theorem preservesColimitsOfShape_rightDerivedLowerStar_of_isProper {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (K : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete K) (R((g)_*[ModuleCat.{u + 1} Λ])) :=
  sorry

end Etale

end AlgebraicGeometry
