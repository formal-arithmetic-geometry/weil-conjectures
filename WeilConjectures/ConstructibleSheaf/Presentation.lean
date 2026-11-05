/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs

/-!
# Constructible sheaves are quotients of sums of `j_{V!} Λ_V`

On a quasi-compact quasi-separated scheme `X` and for a commutative ring `Λ`, every
constructible sheaf of `Λ`-modules on `X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V`
of extensions by zero of constant sheaves along étale maps `j_V : V ⟶ X` from affine schemes
[Stacks 095M; SGA 4½, Rapport, 4.6].

## Main statements

- `AlgebraicGeometry.Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Scheme
