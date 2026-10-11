/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension at a point of a polynomial quotient

Source: Stacks Project, Algebra, Tags 00P2, 00P1, 00OP, and the opening of Tag 00SC
(blueprint: lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference).
-/

universe u

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Tag 00P2 (`lemma-codimension`), applied to a polynomial
quotient; Tags 00P1 and 00OP give dimension n at every point of the polynomial spectrum.
This is the dimension identity used at the opening of Tag 00SC (`lemma-lci`).
(blueprint: lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference).

The heights of q in the quotient and its inverse image in the polynomial ring are finite
natural numbers h and h' (so 0 ≤ h), with h ≤ h' ≤ n; the local topological dimension
is n - h' + h.

Proof (the seven steps of the node):
1. The polynomial ring P and its quotient S are finite type k-algebras
   (`def-weil-pbc-finite-type-algebra`). P is a domain by
   `lem-weil-pbc-polynomial-ring-domain`, so its only minimal prime is zero.
   The inverse image q' of q under the quotient map is prime and contains I.
2. Apply `lem-weil-pbc-dimension-at-point-local-ring-trdeg` (00P1) to S at q and P at q'.
   Identify the local-ring dimensions with the heights by
   `lem-weil-pbc-localization-dimension-chains-below-prime`. Thus both heights are finite,
   and each local topological dimension is its height plus the residue-field trdeg.
3. By `lem-weil-pbc-localization-at-prime-of-quotient`, the quotient map induces a
   surjection P_q' → S_q. Composing with the residue map has kernel the maximal ideal
   q'P_q': the kernel is proper and hence lies in the maximal ideal, and the reverse
   inclusion follows directly from the definition of q'. It therefore identifies the
   residue fields as k-algebras. Algebraic independence is preserved, so their trdegs agree
   (`def-kun-transcendence-degree`).
4. Subtract the two finite dimension identities to obtain 00P2: the difference of the
   local topological dimensions equals h' - h.
5. By `lem-weil-pbc-dimension-at-point-components`, the dimension at q' of Spec P is
   dim P, since zero is the only minimal prime. Choose a maximal ideal using
   `lem-weil-pbc-proper-ideal-contained-in-maximal`. By
   `lem-weil-pbc-finite-type-domain-dimension-local-ring`, dim P is its local-ring dimension
   there, which is n by `lem-weil-pbc-polynomial-ring-maximal-localization-dimension` (00OP).
6. Steps 4 and 5 give dim_q Spec S = n - h' + h. The 00P1 identity at q' also gives
   n = h' + trdeg_k κ(q'), so h' ≤ n.
7. Lift any strict prime chain below q along the surjective quotient map. Inverse images
   are prime and remain strict: equal inverse images would give equal ideals by
   surjectivity. Their last member lies below q'. Taking suprema gives h ≤ h'. Both
   heights are nonnegative since the single-prime chain has length zero. -/
theorem topologicalKrullDimAt_polynomial_quotient_eq_height_difference
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime] :
    ∃ h h' : ℕ,
      q.height = (h : ℕ∞) ∧
      (q.comap (Ideal.Quotient.mk I)).height = (h' : ℕ∞) ∧
      h ≤ h' ∧ h' ≤ n ∧
      topologicalKrullDimAt
        (⟨q, inferInstance⟩ : Spec (CommRingCat.of (MvPolynomial (Fin n) k ⧸ I))) =
        ((n - h' + h : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
