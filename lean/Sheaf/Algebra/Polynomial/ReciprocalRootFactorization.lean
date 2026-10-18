/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Algebra.Polynomial.ReciprocalPolynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Factorization by reciprocal roots

Source: the Weil conjectures blueprint,
`sec-zeta-weil/sk-def-roots/def-weil-ordinary-reciprocal-roots.md`, order 2859,
the nonvanishing and factorization assertions
(blueprint: lem-weil-reciprocal-root-factorization).

Root evaluation and multiplicity are Mathlib's `Polynomial.IsRoot` and
`Polynomial.rootMultiplicity`. The reciprocal polynomial is `Polynomial.reverse`, as in
`Polynomial.reciprocal_polynomial_of_constantCoeff_one`. Reciprocal roots are expressed
by the predicate that a nonzero scalar has inverse a root; the indexed factors use units.
-/

@[expose] public section

universe u v

namespace Polynomial

open Classical in
/-- A polynomial with constant coefficient one has nonzero roots, and inversion bijects
its roots with its reciprocal roots. Over any algebraically closed extension it factors
as a product of `1 - α_j X`, with multiplicities and uniqueness up to reordering.

Source: the Weil conjectures blueprint,
`sec-zeta-weil/sk-def-roots/def-weil-ordinary-reciprocal-roots.md`, order 2859
(blueprint: lem-weil-reciprocal-root-factorization).

Proof plan (the seven steps of the DAG node):
1. A homomorphism of fields is injective. Apply
   lem-weil-coefficientwise-extension-degree to preserve degree and constant coefficient.
   The mapped polynomial is nonzero, and its evaluation is the original `eval₂`.
2. Zero cannot be a root because evaluation there is one. Inversion is an involution
   on nonzero field elements, giving the asserted bijection (def-weil-polynomial-root).
3. Apply lem-weil-alg-closed-linear-factorization to the mapped polynomial. Comparing
   degrees gives exactly `P.natDegree` roots, and step 2 makes every one nonzero.
4. Replace each root β by its inverse α and rewrite `X - β = -β (1 - α X)`.
   Evaluating the resulting product at zero makes its scalar prefactor one.
5. For any such factorization, rewrite each factor as `-α (X - α⁻¹)`.
   By lem-weil-root-multiplicity-mul and lem-weil-root-multiplicity-pos-iff, its
   multiplicity at γ is the number of indices with `α_j⁻¹ = γ`; nonzero constants
   have multiplicity zero and `X - γ` has multiplicity one (def-weil-root-multiplicity).
6. Reverse the product using lem-weil-polynomial-reflection-multiplicative:
   the reversal is the product of `X - α_j`. Step 5 now computes its multiplicities
   at α and identifies them with the original multiplicities at `α⁻¹`.
   The reciprocal polynomial is the one in lem-weil-reciprocal-polynomial.
7. Equal counts at every unit give a permutation between any two factor families.
   By lem-weil-root-multiplicity-pos-iff, a unit occurs exactly when its inverse is
   a root. The indexing type `Fin P.natDegree` counts all factors with multiplicity.
-/
theorem reciprocal_root_factorization {K : Type u} [Field K]
    {L : Type v} [Field L] [IsAlgClosed L] (ι : K →+* L)
    (P : K[X]) (h0 : P.eval 0 = 1) :
    (∀ β : L, (P.map ι).IsRoot β → β ≠ 0) ∧
      Set.BijOn (fun β : L ↦ β⁻¹)
        {β : L | (P.map ι).IsRoot β}
        {α : L | α ≠ 0 ∧ (P.map ι).IsRoot α⁻¹} ∧
      (∃ α : Fin P.natDegree → Lˣ,
        P.map ι = ∏ j, (1 - C (↑(α j) : L) * X)) ∧
      (∀ α : Fin P.natDegree → Lˣ,
        P.map ι = ∏ j, (1 - C (↑(α j) : L) * X) →
          (∀ a : Lˣ,
            Fintype.card {j : Fin P.natDegree // α j = a} =
              rootMultiplicity (↑a⁻¹ : L) (P.map ι) ∧
            rootMultiplicity (↑a⁻¹ : L) (P.map ι) =
              rootMultiplicity (↑a : L) (P.map ι).reverse) ∧
          (∀ a : Lˣ, (∃ j, α j = a) ↔ (P.map ι).IsRoot (↑a⁻¹ : L)) ∧
          (∀ α' : Fin P.natDegree → Lˣ,
            P.map ι = ∏ j, (1 - C (↑(α' j) : L) * X) →
              ∃ σ : Equiv.Perm (Fin P.natDegree), ∀ j, α' j = α (σ j))) := by
  sorry

end Polynomial
