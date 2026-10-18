/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Filtration

/-!
# Finite-order DVR automorphisms trivial on the residue field and tangent line

Source: Stacks Project, More on Algebra, Tag 09EE, proof of (3), specialized to residue
characteristic zero (blueprint: lem-per-dvr-char-zero-tangent-kernel).
-/

@[expose] public section

universe u

namespace IsDiscreteValuationRing

/-- A finite-order automorphism of a DVR of residue characteristic zero is the identity
if it fixes the residue field and its uniformizer ratio is congruent to one.
The ratio is expressed inside the ring by a unit `v` with `a t = v * t`.

Source: Stacks Project, More on Algebra, Tag 09EE, proof of (3), and Algebra, Tag 00IQ (2)
(blueprint: lem-per-dvr-char-zero-tangent-kernel).

Proof:
1. Write `a t = v * t`, with `v - 1` in the maximal ideal `m`. Since `m = (t)`,
   for `x = t^i * b` in `m^i` the identity
   `a x - x = t^i * ((v^i - 1) * a b + (a b - b))` puts the difference in `m^(i+1)`.
   For `i = 0` use `v^0 - 1 = 0`; otherwise factor `v^i - 1` by `v - 1`.
   Thus `a` also preserves `m^i` (def-sc-discrete-valuation-ring).
2. Induction on `j` shows `a^j x - x` belongs to `m^(i+1)` for `x` in `m^i`:
   the zero iterate is immediate; add `a (a^j x) - a^j x` to the previous difference.
3. A DVR is a PID, hence Noetherian (def-weil-pbc-noetherian-ring), and `C` is generated
   as a module by `1`. Its maximal ideal is its Jacobson radical. Krull intersection
   (lem-weil-pbc-krull-intersection-jacobson, Tag 00IQ (2)) gives intersection of all
   `m^n` equal to zero. If `d = a c - c` is nonzero, choose the least `r` with
   `d` not in `m^r`. As `d` is in `m`, `r` is at least two. Set `i = r - 1`;
   then `d` belongs to `m^i` but not to `m^(i+1)`.
4. For a positive `N` with `a^N = 1`, telescope to get
   `0 = a^N c - c = sum (j < N), a^j d`. Step 2 makes this congruent to `N * d`
   modulo `m^(i+1)`. Thus `N * d` belongs to `m^(i+1)`.
5. Write `d = t^i * b` and `N * d = t^(i+1) * e`. Here `b` is not in `m` and `t`
   is nonzero. Cancellation gives `N * b = t * e`. In the residue field this says
   the product of the nonzero natural number `N` and the nonzero residue of `b` is zero,
   contradicting residue characteristic zero. Therefore every `a c = c`, giving `a = id`.
-/
theorem eq_refl_of_finiteOrder_residue_tangent_charZero
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [CharZero (IsLocalRing.ResidueField C)]
    (t : C) (ht : IsLocalRing.maximalIdeal C = Ideal.span {t})
    (a : C ≃+* C) (hfinite : ∃ N : ℕ, 0 < N ∧ a ^ N = 1)
    (hresidue : ∀ c : C, a c - c ∈ IsLocalRing.maximalIdeal C)
    (htangent : ∃ v : Cˣ, a t = (v : C) * t ∧
      (v : C) - 1 ∈ IsLocalRing.maximalIdeal C) :
    a = RingEquiv.refl C := by
  sorry

end IsDiscreteValuationRing
