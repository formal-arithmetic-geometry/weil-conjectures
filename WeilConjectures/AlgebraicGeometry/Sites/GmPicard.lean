/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The Picard group as first étale cohomology of `𝔾ₘ`

For a scheme `X` the isomorphism classes of invertible `𝒪_X`-modules are in bijection with the
cohomological Picard group `H¹(X_ét, 𝔾ₘ)`.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`: there is a bijection
  `Pic(X) ≃ H¹(X_ét, 𝔾ₘ)` (no canonical map yet).

## TODO

`AlgebraicGeometry.Scheme.Pic` carries no group structure yet, and the torsor classification
(blueprint: `lem-sc-torsor-h1`) is not available, so the comparison is recorded as the existence
of a bijection of sets. Replace it by the canonical additive equivalence `L ↦ [Isom(𝒪, L)]`,
of type `≃+`, once both are available.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- **The Picard group is `H¹(X, 𝔾ₘ)`.** For a scheme `X` the isomorphism classes of invertible
`𝒪_X`-modules are in bijection with the cohomological Picard group `H¹(X_ét, 𝔾ₘ)`.

This only asserts that some bijection exists; it does not specify the canonical map
`L ↦ [Isom(𝒪, L)]` of the blueprint statement.
(blueprint: `lem-sc-h1-gm-pic`) -/
theorem nonempty_equiv_cohomologicalPicardGroup (X : Scheme.{u}) :
    Nonempty (X.Pic ≃ X.CohomologicalPicardGroup) :=
  -- Proof sketch: send `L` to the class of the `𝔾ₘ`-torsor `Isom(𝒪_X, L)`; Zariski and étale
  -- `𝔾ₘ`-torsors agree by fpqc descent for invertible modules (Hilbert 90).
  sorry

end AlgebraicGeometry.Scheme
