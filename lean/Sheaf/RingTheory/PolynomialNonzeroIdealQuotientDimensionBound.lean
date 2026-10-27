/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Dimension bound for a nonzero polynomial ideal quotient

Source: Stacks Project, Algebra, Tag 00QK, proof, final nonzero residue-polynomial
kernel inference (blueprint: lem-trf-polynomial-nonzero-ideal-quotient-dimension-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

/-- A quotient of a polynomial ring in `n ≥ 1` variables over a field by an ideal containing
 a nonzero polynomial has Krull dimension at most `n - 1`. The unit ideal is allowed:
 its quotient is the zero ring, whose dimension is `⊥`.

Source: Stacks Project, Algebra, Tag 00QK, proof, final nonzero residue-polynomial
kernel inference (blueprint: lem-trf-polynomial-nonzero-ideal-quotient-dimension-bound).

Proof plan:
1. A field has only the zero and unit ideals, so it is Noetherian and has dimension zero
   (def-weil-pbc-noetherian-ring and def-weil-pbc-krull-dimension-ring).
2. The Noetherian polynomial dimension formula gives dimension `n` for the source ring
   (lem-sf-noetherian-polynomial-dimension).
3. Choose a nonzero `f ∈ I`. The polynomial ring is a domain, so `f` is a nonzerodivisor
   (lem-weil-pbc-polynomial-ring-domain). The quotient map is surjective with kernel `I`
   (def-weil-pbc-algebra-hom-quotient), and therefore kills `f`.
4. Apply the surjective-kernel dimension inequality to obtain `dim (P / I) + 1 ≤ n`
   (lem-trf-surjective-kernel-nonzerodivisor-dimension-drop).
5. If the quotient is zero its dimension is bottom. Otherwise its dimension lies in `ℕ∞`;
   the preceding finite bound excludes infinity. Writing its dimension as `m`, the bound
   becomes `m + 1 ≤ n`, hence `m ≤ n - 1` since `n ≥ 1`.
-/
theorem ringKrullDim_quotient_le_pred_of_exists_mem_ne_zero
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∃ f : MvPolynomial (Fin n) k, f ∈ I ∧ f ≠ 0) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ I) ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

end MvPolynomial
