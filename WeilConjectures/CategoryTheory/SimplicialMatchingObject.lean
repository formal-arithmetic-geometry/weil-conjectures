/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Matching boundary diagram of a simplicial object

This file defines the multicospan shape and index used to describe the matching boundary
of a simplicial object.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- The shape of the multicospan diagram of pairs `i < j` of faces of an `(n + 2)`-simplex. -/
def matchingBoundaryShape (n : ℕ) : MulticospanShape where
  L := Fin (n + 3)
  R := {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2}
  fst p := p.val.1
  snd p := p.val.2

/-- The multicospan index of a simplicial object `K` in degree `n`, with the `n + 3` faces
`K _⦋n + 1⦌` on the left, the pairs `i < j` of faces on the right, and the face maps
`δ` as the two maps from each face to the pairwise intersections. -/
def matchingBoundaryIndex {C : Type u} [Category.{v} C] (K : SimplicialObject C) (n : ℕ) :
    MulticospanIndex (matchingBoundaryShape n) C where
  left _ := K _⦋n + 1⦌
  right _ := K _⦋n⦌
  fst p := K.δ (p.val.2.pred (Fin.ne_zero_of_lt p.property))
  snd p := K.δ (p.val.1.castLT (Nat.lt_of_lt_of_le p.property
    (Nat.le_of_lt_succ p.val.2.isLt)))

end CategoryTheory.SimplicialObject
