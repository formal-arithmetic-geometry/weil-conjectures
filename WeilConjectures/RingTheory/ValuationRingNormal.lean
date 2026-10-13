/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Valuation rings are normal domains

Source: Stacks Project, Algebra, Lemma 10.50.3 (Tag 00IC)
(blueprint: lem-weil-pbc-valuation-ring-normal).
-/

@[expose] public section

universe u v

/-- A domain satisfying the element-or-inverse criterion in its fraction field is normal.
Source: Stacks Project, Algebra, Lemma 10.50.3 (Tag 00IC)
(blueprint: lem-weil-pbc-valuation-ring-normal).

Proof (the direct monic-equation argument recorded in the node):
1. Let `x` in `K` be integral over `A`. If `x = 0`, it is the image of zero. Otherwise,
   choose a monic equation of degree `n ≥ 1` for `x` with coefficients in `A`.
   Degree zero is impossible in the field `K`.
2. The valuation criterion says either `x` lies in `A`, which finishes the argument,
   or `y = x⁻¹` lies in `A`. In the latter case multiply the monic equation by
   `x⁻¹ ^ (n - 1)`. This expresses `x` as the negative sum of the lower coefficients
   times powers of `y`, hence as an element of `A`. The formula includes `n = 1`.
3. Every integral element of `K` therefore lies in `A`. By `isIntegrallyClosed_iff`,
   this is `IsIntegrallyClosed A`; together with the given domain property it is the
   normal-domain notion of `def-weil-pbc-normal-ring` (Stacks Tag 0309). -/
theorem isDomain_isIntegrallyClosed_of_fractionField_element_or_inverse
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (h : ∀ x : K, x ≠ 0 →
      (∃ a : A, algebraMap A K a = x) ∨ (∃ a : A, algebraMap A K a = x⁻¹)) :
    IsDomain A ∧ IsIntegrallyClosed A := by
  sorry
