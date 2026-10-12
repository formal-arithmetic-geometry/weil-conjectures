module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

universe u

open MvPolynomial

namespace MvPolynomial

/-- Coefficient membership criterion for the coordinate ideal.
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 07DW.
(blueprint: new-polynomial-ideal-coefficients-membership)
The proof follows the coefficient comparison and finite monomial decomposition in the
source: coefficients of each generator product are multiples of the corresponding
`g`, and conversely each coefficient in the indicated span is expanded into such
multiples and its monomial is factored by the relevant variable. -/
theorem ideal_coefficients_monomial_membership
    {R : Type u} [CommRing R] (r i : ℕ) (hr : 1 ≤ r) (hir : i ≤ r)
    (g : Fin i → R)
    (p : MvPolynomial (Fin r) R) :
    p ∈ Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j)) ↔
      ∀ E : Fin r →₀ ℕ,
        coeff E p ∈ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}) := by
  sorry

end MvPolynomial
