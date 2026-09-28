/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The Picard group as the first étale cohomology of `𝔾ₘ`

The isomorphism classes of invertible `𝒪_X`-modules, `AlgebraicGeometry.Scheme.Pic`, are in
bijection with `H¹(X_ét, 𝔾ₘ)`, `AlgebraicGeometry.Scheme.CohomologicalPicardGroup`.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`: `Pic(X) ≅ H¹(X_ét, 𝔾ₘ)`.

## TODO

`AlgebraicGeometry.Scheme.Pic` carries no group structure yet (it awaits the tensor product of
invertible modules), so the comparison is recorded as a bijection of sets. Once the group
structure exists it should be upgraded to an `AddEquiv`-type isomorphism, and the map should be
named: it sends `𝓛` to the class of the torsor `Isom(𝒪_X, 𝓛)`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- **The Picard group is `H¹(X_ét, 𝔾ₘ)`.** For a scheme `X` the isomorphism classes of
invertible `𝒪_X`-modules are in bijection with `H¹(X_ét, 𝔾ₘ)`, the class of `𝓛` going to the
class of the `𝔾ₘ`-torsor `Isom(𝒪_X, 𝓛)`.

This factors through `H¹(X_Zar, 𝒪_X^×)`: invertible modules are the Zariski
`𝒪_X^×`-torsors, first cohomology classifies torsors, and a `𝔾ₘ`-torsor trivial on an étale
cover is trivial on a Zariski cover by faithfully flat descent (Hilbert 90). The blueprint
states it for a curve; nothing in the argument is specific to curves.
(blueprint: `lem-sc-h1-gm-pic`) -/
@[stacks 040E]
theorem nonempty_equiv_cohomologicalPicardGroup (X : Scheme.{u}) :
    Nonempty (X.Pic ≃ X.CohomologicalPicardGroup) :=
  sorry

end AlgebraicGeometry.Scheme
