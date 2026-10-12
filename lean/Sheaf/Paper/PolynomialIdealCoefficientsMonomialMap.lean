module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

universe u

open MvPolynomial

namespace MvPolynomial

/-- Coefficient quotient map and induced quotient isomorphism for the coordinate ideal.
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 07DW.
(blueprint: new-polynomial-ideal-coefficients-map)
The coefficient map is formed componentwise into the ideal quotients; finite support
of a polynomial gives its codomain in the direct sum, monomials give surjectivity,
and the preceding coefficient-membership criterion identifies its kernel. The
first isomorphism theorem for modules then supplies the displayed quotient
isomorphism, characterized by the quotient map. -/
theorem ideal_coefficients_monomial_map
    {R : Type u} [CommRing R] (r i : ℕ) (hr : 1 ≤ r) (hir : i ≤ r)
    (g : Fin i → R) :
    ∃ Φ : MvPolynomial (Fin r) R →ₗ[R]
          Π₀ E : Fin r →₀ ℕ, R ⧸ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}),
        (∀ q E, Φ q E = Ideal.Quotient.mk _ (coeff E q)) ∧
        Function.Surjective Φ ∧
        LinearMap.ker Φ = Submodule.restrictScalars R
          (Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))) ∧
        ∃ e : (MvPolynomial (Fin r) R ⧸
            Ideal.span (Set.range fun j : Fin i => C (g j) * X (Fin.castLE hir j))) ≃ₗ[R]
            Π₀ E : Fin r →₀ ℕ, R ⧸ Ideal.span (g '' {j : Fin i | E (Fin.castLE hir j) ≠ 0}),
          ∀ q, e (Ideal.Quotient.mk _ q) = Φ q := by
  sorry

end MvPolynomial
