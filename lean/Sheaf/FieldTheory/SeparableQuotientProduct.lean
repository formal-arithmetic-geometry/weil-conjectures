/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.PolynomialDistinctLinearCRT

/-!
# Evaluation decomposition of a separable polynomial quotient

Source: Stacks Project, Algebra, Tag 00U3 (lemma-etale-over-field), separable polynomial
case and Chinese remainder factorization
(blueprint: lem-pc-separable-polynomial-alg-closed-quotient-product).
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Source: Stacks Project, Algebra, Tag 00U3 (lemma-etale-over-field), separable polynomial
case and Chinese remainder factorization
(blueprint: lem-pc-separable-polynomial-alg-closed-quotient-product).

Proof outline:
1. Apply `lem-pc-separable-polynomial-distinct-roots-alg-closed` to factor the mapped monic
polynomial into distinct linear factors and count its roots: there are exactly `n`.
2. Apply `lem-pc-polynomial-quotient-distinct-linear-crt` to these factors. The Chinese
remainder isomorphism sends the class of each polynomial `q` to its values at the roots.
3. Index the factors by the root set itself. The count from step 1 and the evaluation formula
from step 2 give both assertions. This also includes the empty product when `n = 0`. -/
theorem exists_eval_quotient_algEquiv_pi_of_separable
    {F : Type u} [Field F] {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (P : F[X]) (n : ℕ) (hmonic : P.Monic) (hsep : P.Separable) (hdegree : P.natDegree = n) :
    Nat.card {ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0} = n ∧
      ∃ e : (Ω[X] ⧸ Ideal.span {P.map (algebraMap F Ω)}) ≃ₐ[Ω]
          ({ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0} → Ω),
        ∀ (q : Ω[X]) (ρ : {ρ : Ω // (P.map (algebraMap F Ω)).eval ρ = 0}),
          e (Ideal.Quotient.mk (Ideal.span {P.map (algebraMap F Ω)}) q) ρ = q.eval ρ.val := by
  sorry

end Polynomial
