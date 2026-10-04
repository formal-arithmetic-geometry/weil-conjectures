/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separated local isomorphisms onto an irreducible reduced scheme

Let `p : V ⟶ S` be a separated local isomorphism into an irreducible reduced scheme `S`. Then
`V` is the disjoint union of opens each of which maps isomorphically onto an open of `S`.

The pieces are indexed by the points of `V` over the generic point `η` of `S`: the piece of such
a point `v` consists of all specialisations of `v`. Every point `x` of `V` has a neighbourhood
mapping isomorphically onto an open of `S`; that open contains `η`, so the neighbourhood contains
exactly one point over `η`, which is the unique point of `V` over `η` specialising to `x`. This
shows the pieces are open and partition `V`. Each piece maps injectively to `S`: two local
sections of `p` through points of the same piece agree on a dense open, hence agree by
separatedness of `p` and reducedness of `S`
(`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`).

## Main results

- `AlgebraicGeometry.IsLocalIso.exists_opens_isOpenImmersion`: the decomposition above, with
  nonempty pieces.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated local isomorphism `p : V ⟶ S` into an irreducible reduced scheme `S` is a
disjoint union of open immersions: there is a family of nonempty, pairwise disjoint opens
`U i` of `V` covering `V` such that each `(U i).ι ≫ p` is an open immersion. -/
theorem IsLocalIso.exists_opens_isOpenImmersion {V S : Scheme.{u}} [IrreducibleSpace S]
    [IsReduced S] (p : V ⟶ S) [IsLocalIso p] [IsSeparated p] :
    ∃ (ι : Type u) (U : ι → V.Opens), (∀ i, (U i : Set V).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ i, U i) = ⊤ ∧
      ∀ i, IsOpenImmersion ((U i).ι ≫ p) :=
  sorry

end AlgebraicGeometry
