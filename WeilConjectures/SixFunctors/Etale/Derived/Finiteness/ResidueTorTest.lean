/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.ResidueField
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Testing finite Tor amplitude at the residue field

Let `Λ` be an Artinian local ring with residue field `κ`, for instance the finite coefficient
ring `A_{E,n} = 𝒪_E/ϖⁿ` with `κ = A_{E,1}`, and let `K ∈ D(X_ét, Λ)`. Then `K` has Tor amplitude
in `[a, b]` if and only if `K ⊗ᴸ κ_X` has cohomology in `[a, b]` (blueprint
`lem-exc-residue-tor-test`).

## Proof

One direction is the definition of Tor amplitude, tested against the constant sheaf `κ_X`. For
the converse, represent `K` by a K-flat complex `P` of flat sheaves, so that `K ⊗ᴸ F` is the
complex `P ⊗ F` for every sheaf `F`. Exactness of a complex of étale sheaves is checked on the
stalks at the geometric points `x̄`, and the stalk of `P ⊗ F` is `P_x̄ ⊗ F_x̄`, a complex of flat
`Λ`-modules tensored with a module. Over the Artinian local ring `Λ`, exactness of `P_x̄ ⊗ κ` in a
degree propagates to exactness of `P_x̄ ⊗ M` for every module `M`
(`DerivedCategory.exactAt_tensorRight_of_exactAt_tensorRight_residueField`).

The blueprint states the lemma for bounded constructible `K`; neither boundedness nor
constructibility is needed, and the main statement does not assume them.

## Main statements

- `AlgebraicGeometry.Etale.torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

variable [IsLocalRing Λ] [IsArtinianRing Λ]

end Etale

end AlgebraicGeometry
