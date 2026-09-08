/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.AlgebraicGeometry.ChowLemma.Glue
public import WeilConjectures.AlgebraicGeometry.ChowLemma.Reduction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

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

## Main definitions

- `AlgebraicGeometry.ChowModification` — the Chow modification `X'` of `f : X ⟶ S`.
- `AlgebraicGeometry.ChowModification.index` — the index type of the homogeneous coordinates
  of the projective space the Chow modification embeds into.
- `AlgebraicGeometry.ChowModification.modificationMap` — the modification `X' ⟶ X`.
- `AlgebraicGeometry.ChowModification.toProjectiveSpace` — the immersion `X' ⟶ ℙ(index f; S)`.

## Main statements

- `AlgebraicGeometry.ChowModification.isProper_modificationMap` and
  `AlgebraicGeometry.ChowModification.surjective_modificationMap` — the modification is proper
  and surjective.
- `AlgebraicGeometry.ChowModification.isImmersion_toProjectiveSpace` and
  `AlgebraicGeometry.ChowModification.toProjectiveSpace_over` — the morphism to projective
  space is an immersion over `S`.
- `AlgebraicGeometry.ChowModification.exists_dense_isIso_restrict` — the modification is an
  isomorphism over a dense open subset of `X`.
- `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace` — if `f` is proper,
  the immersion into projective space is a closed immersion, so `X` is dominated by a
  projective `S`-scheme.
- `AlgebraicGeometry.ChowModification.nonempty_data` — the assembly of the above out of the
  reduction, the graph and the gluing; all of the declarations listed here are read off it.

## Implementation notes

* The construction depends on a great many choices — a reduction of `X`, a proper closed model
  of each member of its affine cover, and a closed immersion of the resulting graph into a
  single projective space — and `ChowModification f`, `index f`, `modificationMap f` and
  `toProjectiveSpace f` are four separate declarations that must all be read off the *same*
  choice. The choice is therefore made once, in
  `AlgebraicGeometry.ChowModification.data f : ChowModification.Data f`, and every declaration
  of this file is a field of it.
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

* Deduce the classical form of Chow's lemma for an irreducible `X`, where the modification can
  be taken to be irreducible as well.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200)

## Blueprint

The declarations of this file implement `thm:chow-lemma` of the proper-base-change blueprint.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

namespace ChowModification

/-- All the data the Chow modification of `f : X ⟶ S` is made of, in one structure: the
modification `X'` together with the proper surjective `π : X' ⟶ X`, which is an isomorphism
over a dense open subset of `X`, and the immersion of `X'` into a projective space `ℙ(N; S)`
over `S`.

Bundling the data like this is what makes the choices underlying `ChowModification f`,
`ChowModification.index f`, `ChowModification.modificationMap f` and
`ChowModification.toProjectiveSpace f` the *same* choices: all four are fields of
`ChowModification.data f`. -/
structure Data {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] where
  /-- the modification `X'` -/
  X' : Scheme.{u}
  /-- the proper surjective morphism `X' ⟶ X` -/
  π : X' ⟶ X
  [isProper_π : IsProper π]
  [surjective_π : Surjective π]
  /-- the index type of the homogeneous coordinates of the ambient projective space -/
  N : Type u
  [finite_N : Finite N]
  /-- the immersion of `X'` into the projective space `ℙ(N; S)` -/
  e : X' ⟶ ℙ(N; S)
  [isImmersion_e : IsImmersion e]
  /-- the immersion is a morphism over `S` -/
  w : e ≫ ℙ(N; S) ↘ S = π ≫ f
  /-- the modification is an isomorphism over a dense open subset of `X` -/
  exists_dense_isIso : ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (π ∣_ U)

/-- **Chow's lemma**: a separated morphism of finite type over a Noetherian scheme admits a
Chow modification.

Steps 1 and 2 of Stacks' proof produce a reduction `R` of `X` (`AlgebraicGeometry.ChowReduction`)
with a nonempty finite affine open cover `R.U`, step 3 a proper closed model `M i` of each
member of the cover, step 4 the graph `ChowGraph M` of the family, and steps 5 and 6 the
modification `ChowGraph.modificationMap M` obtained by gluing the projections of the graph,
which is proper and surjective and an isomorphism over `⋂ i, R.U i`; step 7 is the closed
immersion of the graph into a single projective space over `S`. All that is left here is to
assemble these into a `Data f`, transporting the modification along the closed immersion
`R.c : R.Y ⟶ X` and the isomorphism from `⋂ i, R.U i` to the dense open `R.V` of `X`.
(blueprint: `thm:chow-lemma`) -/
@[stacks 0200]
theorem nonempty_data : Nonempty (Data f) := by
  -- Steps 1 and 2: a reduction of `f` with a nonempty finite affine open cover.
  obtain ⟨R, hι⟩ := exists_chowReduction_nonempty_index f
  have : Nonempty R.ι := hι
  have : IsLocallyNoetherian R.Y := LocallyOfFiniteType.isLocallyNoetherian (R.c ≫ f)
  have : CompactSpace R.Y := QuasiCompact.compactSpace_of_compactSpace (R.c ≫ f)
  have : IsNoetherian R.Y := ⟨⟩
  -- Step 3: a proper closed model of each member of the cover.
  have M (i) : ProperClosedModel ((R.U i).ι ≫ R.c ≫ f) :=
    have : IsAffine (R.U i) := R.isAffineOpen_U i
    have : NoetherianSpace (R.U i) :=
      inferInstanceAs (NoetherianSpace ((R.U i : R.Y.Opens) : Set R.Y))
    (nonempty_properClosedModel _).some
  -- Step 7: the graph is a closed subscheme of a single projective space over `S`.
  obtain ⟨N, hNfin, g, hg, hgS⟩ := ChowGraph.exists_isClosedImmersion_over M
  -- Step 5: the modification is proper and surjective, the cover being a cover of `R.Y`.
  have : IsProper (ChowGraph.modificationMap M) :=
    ChowGraph.isProper_modificationMap M R.iSup_U
  have : Surjective (ChowGraph.modificationMap M) :=
    ChowGraph.surjective_modificationMap M R.iSup_U
  refine ⟨{ X' := (⨆ i, ChowGraph.projPreimage M i).toScheme
            π := ChowGraph.modificationMap M ≫ R.c
            N := N
            e := (⨆ i, ChowGraph.projPreimage M i).ι ≫ g
            w := ?_
            exists_dense_isIso := ?_ }⟩
  · simp only [Category.assoc]
    rw [hgS, ChowGraph.modificationMap_over]
  -- Step 6: the modification is an isomorphism over `⋂ i, R.U i`, which is the preimage of the
  -- dense open `R.V` of `X` along the closed immersion `R.c`.
  · refine ⟨R.V, R.dense_V, ?_⟩
    have : IsIso (ChowGraph.modificationMap M ∣_ R.c ⁻¹ᵁ R.V) := by
      rw [R.preimage_V]
      infer_instance
    rw [morphismRestrict_comp]
    infer_instance

/-- The choice of all the data underlying the Chow modification of `f`. -/
def data : Data f := (nonempty_data f).some

end ChowModification

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
  (ChowModification.data f).X'

namespace ChowModification

/-- The index type of the homogeneous coordinates of the projective space that the Chow
modification of `f` is immersed into. -/
def index {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Type u :=
  (data f).N

/-- The projective space the Chow modification is immersed into is finite dimensional. -/
instance finite_index : Finite (index f) := (data f).finite_N

/-- The modification `X' ⟶ X` of a Chow modification, which is proper and surjective and an
isomorphism over a dense open subset of `X`. -/
def modificationMap : ChowModification f ⟶ X := (data f).π

/-- The immersion `X' ⟶ ℙ(index f; S)` of a Chow modification into a projective space
over `S`. -/
def toProjectiveSpace : ChowModification f ⟶ ℙ(index f; S) := (data f).e

/-- The modification of a Chow modification is proper. -/
instance isProper_modificationMap : IsProper (modificationMap f) := (data f).isProper_π

/-- The modification of a Chow modification is surjective. -/
instance surjective_modificationMap : Surjective (modificationMap f) := (data f).surjective_π

/-- The morphism from a Chow modification to projective space is an immersion, that is, a
locally closed immersion. -/
instance isImmersion_toProjectiveSpace : IsImmersion (toProjectiveSpace f) :=
  (data f).isImmersion_e

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
  (data f).w

/-- **Chow's lemma**: the modification of a Chow modification is an isomorphism over a dense
open subset of `X`.
(blueprint: `thm:chow-lemma`) -/
@[stacks 0200]
theorem exists_dense_isIso_restrict :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (modificationMap f ∣_ U) :=
  (data f).exists_dense_isIso

/-- **Chow's lemma for proper morphisms**: if `f : X ⟶ S` is proper, the immersion of its Chow
modification into projective space is a *closed* immersion. Together with
`AlgebraicGeometry.ChowModification.isProper_modificationMap` and
`AlgebraicGeometry.ChowModification.surjective_modificationMap` this says that a proper scheme
over a Noetherian base is dominated by a projective one.
(blueprint: `cor:chow-lemma-proper`) -/
@[stacks 0202]
instance isClosedImmersion_toProjectiveSpace {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [IsProper f] : IsClosedImmersion (toProjectiveSpace f) := by
  -- `toProjectiveSpace f` composed with the structure morphism of `ℙ(index f; S)` is the proper
  -- morphism `modificationMap f ≫ f`, and the structure morphism is separated, so
  -- `toProjectiveSpace f` is itself proper, hence universally closed
  have : IsProper (toProjectiveSpace f ≫ ℙ(index f; S) ↘ S) := by
    rw [toProjectiveSpace_over]
    infer_instance
  have : IsProper (toProjectiveSpace f) := .of_comp _ (ℙ(index f; S) ↘ S)
  exact .of_universallyClosed _

end ChowModification

end

end AlgebraicGeometry
