/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.RingTheory.Depth
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Depth drops by one modulo a regular element

Source: Stacks Project, Algebra, Lemma 10.72.7, Tag 090R, part (1)
(blueprint: lem-weil-pbc-depth-drops-by-one).
-/

universe u v

namespace IsLocalRing

/-- For a nonzero finite module over a Noetherian local ring, quotienting by a
nonzerodivisor in the maximal ideal gives a nonzero module and lowers the finite,
positive depth by one. Source: Stacks Project, Algebra, Tag 090R, part (1)
(blueprint: lem-weil-pbc-depth-drops-by-one).

Proof (the node's independent Rees/Ext argument, avoiding the source's depth-lemma cycle):
1. Set Q = M/xM. If Q were zero, Nakayama (lem-weil-pbc-nakayama-jacobson) would
   force M = 0, since x belongs to the maximal ideal. Images of a finite generating
   set generate Q (def-weil-finitely-generated-module).
2. The depth bound by support dimension (lem-weil-pbc-depth-le-support-dimension)
   and finite local Krull dimension (lem-weil-pbc-noetherian-local-finite-krull-dimension)
   make the depths d of M and e of Q finite. The singleton x is M-regular
   (def-weil-pbc-regular-sequence), so d is at least one (def-weil-pbc-depth).
3. Apply the long exact Ext sequence (lem-weil-pbc-ext-long-exact-second-variable)
   to 0 → M → M → Q → 0, whose first map is multiplication by x
   (def-weil-pbc-exact-sequence). Write A_i = Ext^i(R/m,M) and B_i = Ext^i(R/m,Q)
   (def-pc-ext). Because x annihilates R/m, it acts as zero on every A_i
   (lem-weil-pbc-ext-annihilator-first-variable). Exactness yields
   0 → A_i → B_i → A_{i+1} → 0.
4. Nakayama gives mM ≠ M and mQ ≠ Q. By the finite supremum definition of depth
   (def-weil-pbc-depth), M has a regular sequence of length d but none of length d+1.
   Rees (lem-weil-pbc-rees-ext-regular-sequence), at d and d+1, gives A_i = 0 for
   i < d and A_d ≠ 0.
5. The short exact sequences give B_i = 0 for i < d-1 and B_{d-1} ≠ 0, including
   d = 1. Rees gives a Q-regular sequence of length d-1 and rules out one of length d.
   Thus e = d-1 by def-weil-pbc-depth. -/
theorem depth_quotSMulTop_of_isSMulRegular {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    Nontrivial (QuotSMulTop x M) ∧
      ∃ d : ℕ, 1 ≤ d ∧ depth (R := R) M = (d : ℕ∞) ∧
        depth (R := R) (QuotSMulTop x M) = ((d - 1 : ℕ) : ℕ∞) := by
  sorry

end IsLocalRing
