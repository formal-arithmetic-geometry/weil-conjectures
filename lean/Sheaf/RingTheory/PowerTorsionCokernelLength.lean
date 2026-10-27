/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Cokernel length for a power-torsion scalar

Source: Stacks Project, Divisors, Tag 0BCR, `lemma-affine-punctured-spec`,
converse proof, the length calculation for Q[f^n] and Q/fQ
(blueprint: lem-sfb-power-torsion-cokernel-length).
-/

@[expose] public section

universe u v

namespace Module

/-- If every element of a module is killed by a positive power of f, and its f-torsion
has finite length, then its quotient by f has length at most that of its f-torsion;
in particular the quotient has finite length.

Source: Stacks Project, Divisors, Tag 0BCR, `lemma-affine-punctured-spec`, converse proof,
the scalar-kernel length calculation (blueprint: lem-sfb-power-torsion-cokernel-length).

Proof:
1. Put K_n = Q[f^n], with K_0 = 0, K_1 = Q[f], and T_n = f^n K_{n+1} contained in K_1.
   Multiplication by f^n gives the short exact sequence
   0 → K_n → K_{n+1} → T_n → 0. The chain definition of module length
   (def-weil-pbc-module-length) bounds length(T_n) by l = length(K_1).
   Additivity (lem-weil-pbc-length-additive-short-exact, Module.length_eq_add_of_exact)
   inductively makes each lambda_n = length(K_n) finite. The inclusions of the K_n
   imply lambda_n ≤ lambda_{n+1} by the same chain definition.
2. Let pi : Q → C = Q/fQ, I_n = pi(K_n), and J_n = f K_{n+1} contained in K_n.
   The kernel of f : K_{n+1} → J_n is K_1. Also K_n intersect fQ equals J_n:
   if x = fy belongs to K_n, then f^{n+1}y = f^n x = 0, and conversely.
   Thus 0 → K_1 → K_{n+1} → J_n → 0 and 0 → J_n → K_n → I_n → 0 are short exact.
   By lem-weil-pbc-length-additive-short-exact, writing j_n = length(J_n) and
   i_n = length(I_n), we get lambda_{n+1} = l + j_n and lambda_n = j_n + i_n.
   All terms are finite; cancel j_n from lambda_n ≤ lambda_{n+1} to obtain i_n ≤ l.
3. Power torsion gives Q = union K_n, hence C = union I_n, both increasing unions.
   For any finite strict chain N_0 < ... < N_s in C, choose one witness in each
   N_j outside N_{j-1}. All finitely many witnesses lie in one I_N. Intersecting
   the chain with I_N preserves its strictness, so s ≤ length(I_N) ≤ l.
   Taking the supremum over strict chains (def-weil-pbc-module-length) gives
   length(C) ≤ l < infinity, proving both conclusions. -/
theorem length_quotSMulTop_le_of_power_torsion
    (R : Type u) [CommRing R] (Q : Type v) [AddCommGroup Q] [Module R Q]
    (f : R) (h_torsion : ∀ q : Q, ∃ n : ℕ, 1 ≤ n ∧ f ^ n • q = 0)
    (h_length : Module.length R (Submodule.torsionBy R Q f) < ⊤) :
    Module.length R (QuotSMulTop f Q) ≤ Module.length R (Submodule.torsionBy R Q f) ∧
      Module.length R (QuotSMulTop f Q) < ⊤ := by
  sorry

end Module
