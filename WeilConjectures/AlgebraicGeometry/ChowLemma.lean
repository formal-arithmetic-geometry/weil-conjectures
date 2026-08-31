/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Chow's lemma

Chow's lemma says that a separated morphism of finite type `f : X ⟶ S` over a Noetherian
scheme `S` is, up to a proper surjective modification of `X`, quasi-projective: there are a
finite index type `n`, a scheme `X'`, a proper surjective morphism `π : X' ⟶ X` and an
immersion `i : X' ⟶ ℙ(n; S)` over `S`, and `π` can moreover be arranged to be an isomorphism
over a dense open subset of `X`. See [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200).

Three points about the formulation.

* `n` is the index type of the *homogeneous* coordinates of `ℙ(n; S)`, so the space Stacks
  writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`. Matching `ProjectiveSpace`, the statement quantifies
  over a finite type `n : Type u` rather than over a natural number.
* Mathlib has no bundled `IsFiniteType` for morphisms of schemes, so Stacks' "of finite type"
  is spelled out as the two hypotheses `LocallyOfFiniteType f` and `QuasiCompact f`.
* The proof is deliberately left as `sorry`; this file states the lemma.

Stacks' route to a proof, for whoever picks it up: cover `X` by finitely many affine opens
`U₁, …, Uₘ` that are of finite type over `S`, so that each `Uᵢ` admits an immersion into some
`ℙ(nᵢ; S)`, and let `U` be their intersection, which is dense in `X` once one has reduced to
`X` irreducible. Take for `X'` the closure of the image of `U` under the induced morphism
`U ⟶ X ×_S ℙ(n₁; S) ×_S ⋯ ×_S ℙ(nₘ; S)`; the projection to `X` is proper and surjective and
is an isomorphism over `U`, while the projection to the product of projective spaces followed
by the Segre embedding is an immersion into a single `ℙ(n; S)`.

## Main statements

- `AlgebraicGeometry.chow_lemma` — Chow's lemma as above, dense open included.
- `AlgebraicGeometry.exists_isProper_surjective_isImmersion_projectiveSpace` — the same
  statement without the dense open, which is the form usually applied.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Chow's lemma**: if `S` is a Noetherian scheme and `f : X ⟶ S` is separated and of finite
type, then there are a finite index type `n`, a scheme `X'`, a proper surjective morphism
`π : X' ⟶ X` and an immersion `i : X' ⟶ ℙ(n; S)` over `S`, such that `π` restricts to an
isomorphism over some dense open subset of `X`.

Finite type is spelled as `LocallyOfFiniteType f` together with `QuasiCompact f`, and the
immersion `i` is a locally closed immersion, as in Stacks.
See [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200). -/
theorem chow_lemma [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : Type u) (_ : Finite n) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ℙ(n; S)),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧ i ≫ ℙ(n; S) ↘ S = π ≫ f ∧
        ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U) := by
  sorry

/-- Chow's lemma, in the form without the dense open subset over which the modification is an
isomorphism: a separated morphism of finite type over a Noetherian scheme becomes an immersion
into a projective space after a proper surjective modification of the source.
See [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200). -/
theorem exists_isProper_surjective_isImmersion_projectiveSpace
    [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : Type u) (_ : Finite n) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ℙ(n; S)),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧ i ≫ ℙ(n; S) ↘ S = π ≫ f := by
  obtain ⟨n, _, X', π, i, hπ, hπ', hi, hcomm, -⟩ := chow_lemma f
  exact ⟨n, ‹_›, X', π, i, hπ, hπ', hi, hcomm⟩

end AlgebraicGeometry
