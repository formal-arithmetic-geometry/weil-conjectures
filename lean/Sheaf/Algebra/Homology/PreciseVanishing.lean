/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Precise vanishing for truncated bounded projective complexes

Source: Stacks Project, Tag 064D (blueprint: lem-pc-ring-precise-vanishing).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe u v w

namespace CategoryTheory

/-- Precise vanishing for maps from a truncated bounded projective complex.
Source: Stacks Project, Tag 064D (blueprint: lem-pc-ring-precise-vanishing).
Proof (Stacks, Tag 064D), following the node's three steps:
1. By `lem-pc-ring-derived-map-representative`, bounded-above projectivity identifies
   morphisms out of `P` in the homotopy category with morphisms out of `Q(P)` in the
   derived category. It suffices to show the former vanish.
2. Use `lem-sf-derived-truncation-triangle` for the standard triangle
   `τ≤(n-1) K → K → τ≥n K →`. The upper truncation is acyclic by `hKvanishing`,
   and the lower truncation is zero in degrees at least `n`. The exact Hom sequence
   of `lem-weil-pbc-hom-into-triangle-exact`, together with the comparison in step 1,
   reduces the assertion to vanishing of maps from `P` to these two truncations.
3. Maps to the lower truncation vanish degreewise: below `n` the source is zero,
   and at or above `n` the target is zero. Maps to the acyclic upper truncation are
   null-homotopic by `lem-pc-ring-projective-into-acyclic-zero`. Exactness and the
   comparison therefore give the required derived-category vanishing.
-/
theorem precise_vanishing
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (P K : CochainComplex A ℤ) (n : ℤ)
    (hPbounded : ∃ a b : ℤ,
      (∀ i : ℤ, i < a → IsZero (P.X i)) ∧
      (∀ i : ℤ, b < i → IsZero (P.X i)))
    (hPprojective : ∀ i : ℤ, Projective (P.X i))
    (hPtruncated : ∀ i : ℤ, i < n → IsZero (P.X i))
    (hKvanishing : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    ∀ f : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K), f = 0 := by
  sorry

end CategoryTheory
