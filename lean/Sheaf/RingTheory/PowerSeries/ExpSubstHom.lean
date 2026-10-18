/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The formal exponential turns sums into products

Source: Milne, Lectures on Étale Cohomology, §26, p. 151 and proof of Theorem 27.6,
p. 156, the step “move the inner sum outside”; Deligne, La conjecture de Weil I, §1.5,
p. 276, the passage to (1.5.4) (blueprint: lem-weil-power-series-exp-hom).

The exponential of a series `U` is `(PowerSeries.exp R).subst U`. Unit witnesses express
inversion and integer powers without requiring the coefficient ring to be a field.
-/

@[expose] public section

universe u v

namespace PowerSeries

/-- (blueprint: lem-weil-power-series-exp-hom) The formal exponential takes zero to one,
addition to multiplication, negatives to inverses, and finite integer linear combinations
to products of integer powers. The unit witnesses have prescribed underlying power series,
so they are unique and introduce no choice into the identities.

Source: Milne, Lectures on Étale Cohomology, §26, p. 151 and proof of Theorem 27.6,
p. 156; Deligne, La conjecture de Weil I, §1.5, p. 276, passage to (1.5.4).

Proof: Fix a coefficient degree `N`. By the zero constant coefficients, `U^k * W^l`
has no terms below degree `k + l`. The definition of the exponential
[def-weil-power-series-exponential] therefore permits truncation at power `N`.
Expand `(U + W)^r` by the binomial theorem. The rational-algebra identity
`choose r k / r! = 1 / (k! * (r-k)!)` turns its exponential coefficient into the
sum of the coefficients of `U^k * W^l / (k! * l!)`. Reindex by `l = r-k` and add the
zero terms with `k+l > N`. The Cauchy product formula [def-weil-formal-power-series]
identifies this finite sum with the degree-`N` coefficient of `exp(U) * exp(W)`.
For `N = 0` only `k = l = 0` contributes one. Coefficient extensionality proves additivity.
At zero the defining exponential has only its zeroth-power contribution, giving one.
Apply additivity to `U` and `-U` to obtain `exp(U) * exp(-U) = 1`; commutativity gives
the reverse product, hence a unit whose inverse is `exp(-U)`.
Induction on natural numbers now gives `exp(n • U) = exp(U)^n`. For a negative integer,
apply the inverse identity to its positive opposite to obtain the corresponding integer
power in the unit group. Integer multiples retain zero constant coefficient.
Finally induct on the finite family: the empty sum and product give the zero identity;
adjoining one index uses additivity and the integer-multiple identity. Taking the unit
at each index supplies exactly the unit witnesses and the asserted product formula. -/
theorem exp_subst_hom (R : Type u) [CommRing R] [Algebra ℚ R] :
    (exp R).subst (0 : PowerSeries R) = 1 ∧
    (∀ (U W : PowerSeries R), constantCoeff U = 0 → constantCoeff W = 0 →
      (exp R).subst (U + W) = (exp R).subst U * (exp R).subst W) ∧
    (∀ (U : PowerSeries R), constantCoeff U = 0 →
      ∃ e : (PowerSeries R)ˣ,
        (e : PowerSeries R) = (exp R).subst U ∧
        (exp R).subst (-U) = ((e⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) ∧
    (∀ (I : Type v) [Fintype I] (U : I → PowerSeries R) (ε : I → ℤ),
      (∀ i : I, constantCoeff (U i) = 0) →
      ∃ e : I → (PowerSeries R)ˣ,
        (∀ i : I, (e i : PowerSeries R) = (exp R).subst (U i)) ∧
        (exp R).subst (∑ i : I, ε i • U i) =
          ((∏ i : I, e i ^ ε i : (PowerSeries R)ˣ) : PowerSeries R)) := by
  sorry

end PowerSeries
