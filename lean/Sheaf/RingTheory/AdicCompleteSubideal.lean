/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Adic completeness for a finitely generated subideal

Source: Stacks Project, Algebra, Tag 090T (lemma-complete-by-sub), with the module
specialized to the ring itself (blueprint: lem-sfb-adic-complete-subideal).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A ring complete for an ideal is complete for every finitely generated subideal.

Source: Stacks Project, Algebra, Tag 090T (lemma-complete-by-sub), specialization `M = A`.
(blueprint: lem-sfb-adic-complete-subideal)

Proof:
1. By def-weil-pbc-adically-complete-ring, the intersection of the powers of `K` is zero.
   Since every power of `L` is contained in the corresponding power of `K`, the intersection
   of the powers of `L` is zero as well. The `L`-adic completion map is therefore injective.
2. For `f` in `K`, choose representatives `a_n` of a compatible family modulo `f^n`.
   Write `a_n - a_{n+1} = f^n z_n`. The family is compatible modulo `K^n`, so completeness
   for `K` gives `x` with `b_n = a_n - x` in `K^n`, by
   def-weil-pbc-adically-complete-ring.
3. For fixed `n`, the sums `s_c = sum_{j < c} f^j z_{n+j}` are `K`-adically Cauchy.
   Completeness gives `y_n` with `y_n - s_c` in `K^c`. Telescoping gives
   `f^n s_c = b_n - b_{n+c}`, hence `b_n - f^n y_n` belongs to `K^{n+c}` for every `c`.
   Separatedness forces `b_n = f^n y_n`, proving surjectivity for the principal ideal `(f)`.
4. Choose finite generators of `L`; all lie in `K`. Apply
   lem-sfb-adic-surjectivity-from-principal-generators (Stacks Tag 090S) to their principal
   completion maps to obtain surjectivity of the `L`-adic completion map. The empty family
   gives `L = 0`. Combine this with step 1 and def-weil-pbc-adically-complete-ring.
-/
theorem IsAdicComplete.of_fg_subideal (A : Type u) [CommRing A]
    (L K : Ideal A) (hLK : L ≤ K) (hL : L.FG) [IsAdicComplete K A] :
    IsAdicComplete L A := by
  sorry
