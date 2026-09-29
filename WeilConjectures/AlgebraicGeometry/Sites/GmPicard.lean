/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# Invertible sheaves and the first étale cohomology of `𝔾ₘ`

For a scheme `X`, sending an invertible sheaf `L` to the class of the étale `𝔾ₘ`-torsor
`Isom(𝒪_{X_ét}, L_ét)` is a bijection from the set `X.Pic` of isomorphism classes of invertible
`𝒪_X`-modules onto the cohomological Picard group `H¹(X_ét, 𝔾ₘ)`.

## Main definitions

- `AlgebraicGeometry.Scheme.picToCohomologicalPicardGroup`: the canonical map
  `X.Pic → H¹(X_ét, 𝔾ₘ)`, `L ↦ [Isom(𝒪, L)]`.
- `AlgebraicGeometry.Scheme.picEquivCohomologicalPicardGroup`: the resulting bijection
  `X.Pic ≃ H¹(X_ét, 𝔾ₘ)` of sets.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_picToCohomologicalPicardGroup`: the canonical map is
  bijective. This is the étale half of Grothendieck's Hilbert 90.

## TODO

- `AlgebraicGeometry.Scheme.Pic` has no group structure yet, so the comparison is only a
  bijection of sets. Once `Pic` is a group, upgrade it to an additive equivalence `≃+` and prove
  that it is natural in `X` with respect to `Pic.map` and the pullback on cohomology composed
  with `AlgebraicGeometry.Scheme.upperStarGmSheafIso`.
- Prerequisites for the proof, not yet in the project: for an abelian sheaf `G` on a site,
  `H¹(G) = Ext¹(ℤ, G)` classifies `G`-torsors (blueprint: `lem-sc-torsor-h1`); and
  `L ↦ Isom(𝒪, L)` is a bijection from invertible modules to étale `𝔾ₘ`-torsors
  (blueprint: `lem-sc-line-bundle-torsor`).
- The Zariski comparison `H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`, which is also part of the blueprint
  statement, is out of scope here.
- Derive `AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field` from
  `bijective_picToCohomologicalPicardGroup` and the triviality of `Pic` of a field.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The canonical map from the set `X.Pic` of isomorphism classes of invertible sheaves to the
cohomological Picard group `H¹(X_ét, 𝔾ₘ)`: it sends `L` to the class of the étale `𝔾ₘ`-torsor
`Isom(𝒪_{X_ét}, L_ét)`. The construction is `sorry`. -/
noncomputable def picToCohomologicalPicardGroup : X.Pic → X.CohomologicalPicardGroup :=
  -- Construction: the class of the torsor `Isom(𝒪, L)` under `H¹(G) = Ext¹(ℤ, G)`
  -- (blueprint: `lem-sc-torsor-h1`).
  sorry

/-- **Grothendieck's Hilbert 90, étale half.** For a scheme `X`, the map sending an invertible
sheaf `L` to the class of the `𝔾ₘ`-torsor `Isom(𝒪, L)` is a bijection from the set of
isomorphism classes of invertible sheaves `X.Pic` onto `H¹(X_ét, 𝔾ₘ)`.

The blueprint lemma `lem-sc-h1-gm-pic` is the special case of a curve.
(blueprint: `thm-sc-hilbert-90`) -/
theorem bijective_picToCohomologicalPicardGroup :
    Function.Bijective X.picToCohomologicalPicardGroup :=
  -- Proof sketch: (1) `H¹(X_ét, 𝔾ₘ) = Ext¹(ℤ, 𝔾ₘ)` classifies étale `𝔾ₘ`-torsors
  -- (blueprint: `lem-sc-torsor-h1`); (2) `L ↦ Isom(𝒪, L)` is a bijection from invertible
  -- modules to étale `𝔾ₘ`-torsors (blueprint: `lem-sc-line-bundle-torsor`): injectivity is
  -- formal, and surjectivity is étale descent for quasi-coherent modules, which shows that an
  -- étale-locally trivial invertible sheaf is Zariski-locally trivial.
  sorry

/-- The bijection `X.Pic ≃ H¹(X_ét, 𝔾ₘ)` given by the canonical map
`AlgebraicGeometry.Scheme.picToCohomologicalPicardGroup`. -/
noncomputable def picEquivCohomologicalPicardGroup : X.Pic ≃ X.CohomologicalPicardGroup :=
  .ofBijective _ X.bijective_picToCohomologicalPicardGroup

/-- The set of isomorphism classes of invertible sheaves `X.Pic` is in bijection with
`H¹(X_ét, 𝔾ₘ)`. See `AlgebraicGeometry.Scheme.picEquivCohomologicalPicardGroup` for the
canonical bijection. -/
theorem nonempty_equiv_cohomologicalPicardGroup :
    Nonempty (X.Pic ≃ X.CohomologicalPicardGroup) :=
  ⟨X.picEquivCohomologicalPicardGroup⟩

end AlgebraicGeometry.Scheme
