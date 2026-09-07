/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Chow's lemma

Chow's lemma says that a separated morphism of finite type `f : X ⟶ S` over a Noetherian
scheme `S` is, up to a proper surjective modification of `X`, quasi-projective. For such an `f`
we introduce the modification itself: a scheme `AlgebraicGeometry.ChowModification f`, a finite
index type `AlgebraicGeometry.ChowModification.index f` and two morphisms out of the
modification, namely a proper surjective
`AlgebraicGeometry.ChowModification.modificationMap f : ChowModification f ⟶ X` which is an
isomorphism over a dense open subset of `X`, and an immersion
`AlgebraicGeometry.ChowModification.toProjectiveSpace f : ChowModification f ⟶ ℙ(index f; S)`
over `S`.

When `f` is moreover *proper*, both morphisms out of the modification are as good as one could
hope for: the immersion into `ℙ(index f; S)` is a *closed* immersion, and the modification
itself factors as a closed immersion `ChowModification f ⟶ ℙ(index f; X)` followed by the
projection `ℙ(index f; X) ⟶ X`. This is the form of Chow's lemma used in the proof of proper
base change.

## Main definitions

- `AlgebraicGeometry.ChowModification` — the Chow modification `X'` of `f : X ⟶ S`.
- `AlgebraicGeometry.ChowModification.index` — the index type of the homogeneous coordinates
  of the projective space the Chow modification embeds into.
- `AlgebraicGeometry.ChowModification.modificationMap` — the modification `X' ⟶ X`.
- `AlgebraicGeometry.ChowModification.toProjectiveSpace` — the immersion `X' ⟶ ℙ(index f; S)`.
- `AlgebraicGeometry.ChowModification.toProjectiveSpaceOver` — the morphism
  `X' ⟶ ℙ(index f; X)` into projective space over `X` induced by `X' ⟶ X` and
  `X' ⟶ ℙ(index f; S)`.

## Main statements

- `AlgebraicGeometry.ChowModification.isProper_modificationMap` and
  `AlgebraicGeometry.ChowModification.surjective_modificationMap` — the modification is proper
  and surjective.
- `AlgebraicGeometry.ChowModification.isImmersion_toProjectiveSpace` and
  `AlgebraicGeometry.ChowModification.toProjectiveSpace_over` — the morphism to projective
  space is an immersion over `S`.
- `AlgebraicGeometry.ChowModification.exists_dense_isIso_restrict` — the modification is an
  isomorphism over a dense open subset of `X`.
- `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace` — for proper `f`,
  the morphism to `ℙ(index f; S)` is a closed immersion.
- `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpaceOver` — for proper
  `f`, the morphism to `ℙ(index f; X)` is a closed immersion.

## Implementation notes

* The construction of `ChowModification f` and the proofs of its basic properties are `sorry`
  by design: this file only *states* Chow's lemma, and the construction is left to a later
  file. See the `TODO` below for the intended route. The closed-immersion statements for
  proper `f` are proved, but of course inherit those `sorry`s.
* Rather than packaging the modification as a structure and asserting that it is nonempty,
  the modification is a definition and its properties are separate statements. A consumer
  therefore obtains properness of the modification and the immersion property by typeclass
  inference, without destructing an existential.
* `index f` is the index type of the *homogeneous* coordinates of `ℙ(index f; S)`, so the
  space Stacks writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`. Matching
  `AlgebraicGeometry.ProjectiveSpace` and Mathlib's affine space `𝔸(n; S)`, it is a finite
  type in `Type u` rather than a natural number.
* Mathlib has no bundled `IsFiniteType` for morphisms of schemes, so Stacks' "of finite type"
  is spelled out as the two hypotheses `LocallyOfFiniteType f` and `QuasiCompact f`.
* `IsImmersion` is Stacks' immersion (locally closed), not `IsClosedImmersion`.

## TODO

* Construct `ChowModification f` and prove its properties. Stacks' route: cover `X` by
  finitely many affine opens `U₁, …, Uₘ` that are of finite type over `S`, so that each `Uᵢ`
  admits an immersion into some `ℙ(nᵢ; S)`, and let `U` be their intersection, which is dense
  in `X` once one has reduced to `X` irreducible. Take for `ChowModification f` the closure of
  the image of `U` under the induced morphism
  `U ⟶ X ×_S ℙ(n₁; S) ×_S ⋯ ×_S ℙ(nₘ; S)`; the projection to `X` is proper and surjective and
  is an isomorphism over `U`, while the projection to the product of projective spaces
  followed by the Segre embedding is an immersion into a single `ℙ(n; S)`. The immersions of
  the `Uᵢ` need the standard affine charts of `ℙ(n; S)`, which are a `TODO` of
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks, Tag 0202](https://stacks.math.columbia.edu/tag/0202)

## Blueprint

The declarations of this file implement `thm:chow-lemma` of the proper-base-change blueprint.
`ChowModification.isClosedImmersion_toProjectiveSpace` implements
`lemma:weil-pbc-chow-factorization` and `ChowModification.toProjectiveSpaceOver` together with
`ChowModification.isClosedImmersion_toProjectiveSpaceOver` implements
`lemma:weil-pbc-chow-embedding-over-x`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

/-- The **Chow modification** `X'` of a separated morphism of finite type `f : X ⟶ S` over a
Noetherian scheme `S`: a scheme with a proper surjective morphism to `X` which is an
isomorphism over a dense open subset of `X`, and an immersion into a projective space over
`S`, i.e. a scheme making

```
                     toProjectiveSpace
  ChowModification f -----------------> ℙ(index f; S)
          |                                   |
          | modificationMap                   | ↘
          ↓                                   ↓
          X ------------- f ----------------> S
```

commute. -/
@[stacks 0200]
def ChowModification {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Scheme.{u} :=
  sorry

namespace ChowModification

/-- The index type of the homogeneous coordinates of the projective space that the Chow
modification of `f` is immersed into. -/
def index {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Type u :=
  sorry

/-- The projective space the Chow modification is immersed into is finite dimensional. -/
instance finite_index : Finite (index f) := sorry

/-- The modification `X' ⟶ X` of a Chow modification, which is proper and surjective and an
isomorphism over a dense open subset of `X`. -/
def modificationMap : ChowModification f ⟶ X := sorry

/-- The immersion `X' ⟶ ℙ(index f; S)` of a Chow modification into a projective space
over `S`. -/
def toProjectiveSpace : ChowModification f ⟶ ℙ(index f; S) := sorry

/-- The modification of a Chow modification is proper. -/
instance isProper_modificationMap : IsProper (modificationMap f) := sorry

/-- The modification of a Chow modification is surjective. -/
instance surjective_modificationMap : Surjective (modificationMap f) := sorry

/-- The morphism from a Chow modification to projective space is an immersion, that is, a
locally closed immersion. -/
instance isImmersion_toProjectiveSpace : IsImmersion (toProjectiveSpace f) := sorry

/-- The immersion of a Chow modification into projective space is a morphism over `S`:

```
                     toProjectiveSpace
  ChowModification f -----------------> ℙ(index f; S)
          |                                   |
          | modificationMap                   | ↘
          ↓                                   ↓
          X ------------- f ----------------> S
```

commutes. -/
@[reassoc]
theorem toProjectiveSpace_over :
    toProjectiveSpace f ≫ ℙ(index f; S) ↘ S = modificationMap f ≫ f :=
  sorry

/-- **Chow's lemma**: the modification of a Chow modification is an isomorphism over a dense
open subset of `X`.
(blueprint: `thm:chow-lemma`) -/
@[stacks 0200]
theorem exists_dense_isIso_restrict :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (modificationMap f ∣_ U) :=
  sorry

/-- The morphism `ChowModification f ⟶ ℙ(index f; X)` induced by the modification
`modificationMap f : ChowModification f ⟶ X` and the immersion
`toProjectiveSpace f : ChowModification f ⟶ ℙ(index f; S)`, using that `ℙ(index f; X)` is the
fibre product `X ×_S ℙ(index f; S)` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`). -/
def toProjectiveSpaceOver : ChowModification f ⟶ ℙ(index f; X) :=
  ProjectiveSpace.liftBaseChange (modificationMap f) (toProjectiveSpace f)
    (toProjectiveSpace_over f).symm

/-- `toProjectiveSpaceOver f` is a morphism over `X`:

```
                    toProjectiveSpaceOver
  ChowModification f --------------------> ℙ(index f; X)
          |                                      |
          | modificationMap                      | ↘
          ↓                                      ↓
          X ==================================== X
```

commutes. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceOver_over :
    toProjectiveSpaceOver f ≫ ℙ(index f; X) ↘ X = modificationMap f :=
  ProjectiveSpace.liftBaseChange_over _ _ _

/-- `toProjectiveSpaceOver f` recovers `toProjectiveSpace f` after projecting
`ℙ(index f; X) ⟶ ℙ(index f; S)`. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceOver_map :
    toProjectiveSpaceOver f ≫ ProjectiveSpace.map (index f) f = toProjectiveSpace f :=
  ProjectiveSpace.liftBaseChange_map _ _ _

section IsProper

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f]

/-- For a **proper** `f`, the immersion of the Chow modification into projective space is
proper: the composite `ChowModification f ⟶ ℙ(index f; S) ⟶ S` is `modificationMap f ≫ f`,
which is proper, and `ℙ(index f; S) ↘ S` is separated. -/
instance isProper_toProjectiveSpace : IsProper (toProjectiveSpace f) :=
  have : IsProper (toProjectiveSpace f ≫ ℙ(index f; S) ↘ S) := by
    rw [toProjectiveSpace_over]
    infer_instance
  .of_comp _ (ℙ(index f; S) ↘ S)

/-- **The closed-immersion form of Chow's lemma**: for a proper `f : X ⟶ S`, the immersion of
the Chow modification into `ℙ(index f; S)` is a *closed* immersion, being a proper immersion.
Together with `AlgebraicGeometry.ChowModification.toProjectiveSpace_over` this says that
`ChowModification f ⟶ S` factors as a closed immersion into a projective space over `S`
followed by the structure morphism of that projective space.
(blueprint: `lemma:weil-pbc-chow-factorization`) -/
@[stacks 0202]
instance isClosedImmersion_toProjectiveSpace : IsClosedImmersion (toProjectiveSpace f) :=
  .of_isImmersion_of_universallyClosed _

/-- **The projective embedding of a Chow modification over `X`**: for a proper `f : X ⟶ S`,
the morphism `(modificationMap f, toProjectiveSpace f) : ChowModification f ⟶ ℙ(index f; X)`
into `ℙ(index f; X) = X ×_S ℙ(index f; S)` is a closed immersion. Together with
`AlgebraicGeometry.ChowModification.toProjectiveSpaceOver_over` this says that
`modificationMap f : ChowModification f ⟶ X` factors as a closed immersion into a projective
space over `X` followed by the structure morphism of that projective space.
(blueprint: `lemma:weil-pbc-chow-embedding-over-x`) -/
@[stacks 0202]
instance isClosedImmersion_toProjectiveSpaceOver :
    IsClosedImmersion (toProjectiveSpaceOver f) :=
  ProjectiveSpace.isClosedImmersion_liftBaseChange _ _ _

end IsProper

end ChowModification

end

end AlgebraicGeometry
