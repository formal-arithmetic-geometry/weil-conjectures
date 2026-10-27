/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.RingTheory.CoordinateSubmodule
public import Mathlib.Data.Set.Countable

/-!
# Countable coordinate support of a countably generated linear image

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20536 (blueprint: lem-trf-countably-generated-image-support).
-/

@[expose] public section

universe u v w z

open DirectSum

namespace DirectSum

set_option autoImplicit false in
/-- The image of a countably generated module is supported on the countable union of
supports of the images of a generating sequence. No countability assumption is made
on the ring or on the underlying sets of the modules.

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20536 (blueprint: lem-trf-countably-generated-image-support).

Proof:
1. Choose a countable generating subset `G` of `L` and an injection `G → ℕ`.
   Define `g n` to be the generator assigned to `n`, or zero if none is assigned.
   Every generator occurs, so `Submodule.span R (Set.range g) = ⊤`. If `G` is empty,
   then `L` is zero and the zero sequence works.
2. Each image `h (g n)` has finite coordinate support by
   `def-weil-pbc-direct-sum-modules`. Their union is countable: choose injections
   of these finite supports into `ℕ`, assign a coordinate its least occurrence and
   its index in that support, and compose the resulting injection into `ℕ × ℕ`
   with Cantor pairing. This also covers an empty union.
3. Express any `x` as a finite linear combination of the `g n`. Outside the union,
   every corresponding coordinate of `h (g n)` vanishes, so linearity and the
   componentwise direct-sum operations make the coordinate of `h x` zero.
   Thus the support is contained in the union. By `def-trf-coordinate-submodule`
   this is exactly containment of the range in that coordinate submodule.
-/
theorem exists_generatingSequence_countable_image_support
    (R : Type u) [CommRing R] (L : Type v) [AddCommGroup L] [Module R L]
    (J : Type w) (N : J → Type z) [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    (hL : ∃ G : Set L, G.Countable ∧ Submodule.span R G = ⊤)
    (h : L →ₗ[R] (⨁ j, N j)) :
    ∃ g : ℕ → L, Submodule.span R (Set.range g) = ⊤ ∧
      (⋃ n : ℕ, {j : J | (h (g n)) j ≠ 0}).Countable ∧
      (∀ x : L, {j : J | (h x) j ≠ 0} ⊆ ⋃ n : ℕ, {j : J | (h (g n)) j ≠ 0}) ∧
      LinearMap.range h ≤
        coordinateSubmodule R J N (⋃ n : ℕ, {j : J | (h (g n)) j ≠ 0}) := by
  sorry

end DirectSum
