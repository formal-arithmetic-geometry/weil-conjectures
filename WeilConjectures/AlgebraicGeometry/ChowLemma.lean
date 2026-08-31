/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Chow's lemma

Chow's lemma says that a separated morphism of finite type `f : X ⟶ S` over a Noetherian
scheme `S` is, up to a proper surjective modification of `X`, quasi-projective. We package the
data of such a modification in the structure `AlgebraicGeometry.ChowModification f`: a finite
index type `n`, a scheme `X'`, a proper surjective morphism `π : X' ⟶ X` and an immersion
`i : X' ⟶ ℙ(n; S)` over `S`, together with a dense open of `X` over which `π` is an
isomorphism. Chow's lemma is then the assertion that `ChowModification f` is nonempty.

## Main definitions

- `AlgebraicGeometry.ChowModification` — the data of a Chow modification of `f : X ⟶ S`.

## Main statements

- `AlgebraicGeometry.chow_lemma` — **Chow's lemma**: a separated morphism of finite type over
  a Noetherian scheme admits a Chow modification.

## Implementation notes

* `n` is the index type of the *homogeneous* coordinates of `ℙ(n; S)`, so the space Stacks
  writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`. Matching `AlgebraicGeometry.ProjectiveSpace` and
  Mathlib's affine space `𝔸(n; S)`, and matching
  `AlgebraicGeometry.AffineBlowup.exists_isClosedImmersion_comp_projMvPolynomialToSpec`, a
  Chow modification carries a finite type `n : Type u` rather than a natural number.
* Mathlib has no bundled `IsFiniteType` for morphisms of schemes, so Stacks' "of finite type"
  is spelled out as the two hypotheses `LocallyOfFiniteType f` and `QuasiCompact f`.
* `IsImmersion` is Stacks' immersion (locally closed), not `IsClosedImmersion`.
* The properties of `π` and `i` are fields of `ChowModification` and are instances, so a
  consumer of `chow_lemma` obtains them by typeclass inference after destructing the
  `Nonempty`. This follows `AlgebraicGeometry.Compactification` of
  `WeilConjectures.Compactification.Defs`, which packages Nagata's theorem the same way.

## TODO

* The proof of `chow_lemma` is `sorry`; this file only states the lemma. Stacks' route to a
  proof: cover `X` by finitely many affine opens `U₁, …, Uₘ` that are of finite type over `S`,
  so that each `Uᵢ` admits an immersion into some `ℙ(nᵢ; S)`, and let `U` be their
  intersection, which is dense in `X` once one has reduced to `X` irreducible. Take for `X'`
  the closure of the image of `U` under the induced morphism
  `U ⟶ X ×_S ℙ(n₁; S) ×_S ⋯ ×_S ℙ(nₘ; S)`; the projection to `X` is proper and surjective and
  is an isomorphism over `U`, while the projection to the product of projective spaces
  followed by the Segre embedding is an immersion into a single `ℙ(n; S)`. The immersions of
  the `Uᵢ` are built from the standard affine charts
  `AlgebraicGeometry.ProjectiveSpace.chart` of `ℙ(n; S)`; what is still missing is the Segre
  embedding.
* The closed-immersion form of Chow's lemma, [Stacks, Tag 0202]: for proper `f`, the induced
  morphism `X' ⟶ X ×_S ℙ(n; S)` is an immersion by `IsImmersion.of_comp`, and a proper
  immersion is a closed immersion. This is what
  `lemma:weil-pbc-chow-factorization` of the proper-base-change blueprint asks for.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200)

## Blueprint

`chow_lemma` implements `lemma:weil-pbc-chow-noetherian` of the proper-base-change blueprint.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The data of a **Chow modification** of `f : X ⟶ S`: a finite index type `n`, a scheme
`X'`, a proper surjective morphism `π : X' ⟶ X` and an immersion `i : X' ⟶ ℙ(n; S)` making

```
             i
  X' --------------> ℙ(n; S)
  |                     |
  | π                   | ↘
  ↓                     ↓
  X -------- f -------> S
```

commute, together with a dense open subset `U` of `X` over which `π` is an isomorphism. -/
@[stacks 0200]
structure ChowModification where
  /-- The index type of the homogeneous coordinates of the projective space. -/
  n : Type u
  /-- The projective space is finite-dimensional. -/
  finite : Finite n
  /-- The source of the modification. -/
  X' : Scheme.{u}
  /-- The modification, which is proper and surjective. -/
  π : X' ⟶ X
  /-- The immersion of the modification into the projective space over `S`. -/
  i : X' ⟶ ℙ(n; S)
  comm : i ≫ ℙ(n; S) ↘ S = π ≫ f
  isProper : IsProper π
  surjective : Surjective π
  isImmersion : IsImmersion i
  /-- The dense open subset of `X` over which the modification is an isomorphism. -/
  U : X.Opens
  dense : Dense (U : Set X)
  isIso_restrict : IsIso (π ∣_ U)

attribute [instance] ChowModification.finite ChowModification.isProper
  ChowModification.surjective ChowModification.isImmersion ChowModification.isIso_restrict

/-- **Chow's lemma**: if `S` is a Noetherian scheme and `f : X ⟶ S` is separated and of finite
type, then `f` admits a Chow modification, that is, there are a finite index type `n`, a
scheme `X'`, a proper surjective morphism `π : X' ⟶ X` and an immersion `i : X' ⟶ ℙ(n; S)`
over `S` such that `π` restricts to an isomorphism over some dense open subset of `X`.

Finite type is spelled as `LocallyOfFiniteType f` together with `QuasiCompact f`, and the
immersion `i` is a locally closed immersion, as in Stacks.
(blueprint: `lemma:weil-pbc-chow-noetherian`) -/
@[stacks 0200]
theorem chow_lemma [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (ChowModification f) :=
  sorry

end AlgebraicGeometry
