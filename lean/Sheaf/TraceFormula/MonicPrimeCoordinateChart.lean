module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Finite
import Sheaf.TraceFormula.PolynomialShearLeadingCoefficient

/-!
# A monic finite coordinate chart at a nonzero polynomial prime

Source: Stacks Project, Algebra, Tag 051P (`lemma-refined-Noether-normalization`),
nonzero-prime induction step, using Tag 051N (`lemma-helper-polynomial`)
(blueprint: lem-trf-monic-prime-coordinate-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators

namespace Algebra

/-- A triangular shear gives the specified monic finite chart and prime contraction.

Source: Stacks Project, Algebra, Tag 051P (`lemma-refined-Noether-normalization`),
nonzero-prime induction step, using Tag 051N (`lemma-helper-polynomial`)
(blueprint: lem-trf-monic-prime-coordinate-chart).

Here `n = m + 1`, the final variable is `X (Fin.last m)`, and the coefficient ring
`B` is `MvPolynomial (Fin m) k`. The witness `F : Polynomial B` is the expression
of `f` as a polynomial in that final variable: its evaluation under the canonical
inclusion of `B` equals `f`. Thus `F.Monic` and `F.natDegree = d` express monicity
and degree in the final variable, rather than total degree. The equations for
`sigma` and its inverse specify them on every generator. The equation for `psi`
fixes the canonical substitution, and those for `qStar` and `p` fix both ideals.

Proof, following the six steps of the DAG node:
1. Properness of the prime excludes a nonzero constant in it. Therefore `g` is
   nonconstant. Apply `lem-trf-polynomial-shear-leading-coefficient` over `k` to
   obtain positive exponents and a nonzero scalar leading coefficient in positive degree.
2. Use the polynomial evaluation universal property
   (`def-weil-pbc-mv-polynomial-ring`) to construct the shear and its subtractive
   inverse. Their composites fix all variables and scalars, hence are identities.
   Divide the leading coefficient by the nonzero scalar to obtain the monic `F`.
3. Transport the prime by the automorphism. Its inverse tests properness and the
   prime-product condition. The transported ideal contains `sigma g` and hence `f`.
4. Substitute `f` for the final source variable. The monic relation expresses the
   `d`-th power of the final target variable as `psi X` minus lower powers with
   coefficients in `B`. Strong induction expresses every power in the span of the
   first `d` powers: for an exponent at least `d`, multiply that relation by the
   power with exponent reduced by `d`; all resulting exponents are smaller.
   Grouping multivariate monomials by their final exponent gives the displayed
   linear combinations for every element of the target. These finitely many
   generators give finiteness (`def-weil-finitely-generated-module`).
5. Contract `qStar` to `B`; inverse images preserve primality. Expand any `H` as
   its constant coefficient plus the final variable times another polynomial.
   Since `f` belongs to `qStar`, its image belongs to `qStar` exactly when that
   constant coefficient belongs to `p`.
6. The same expansion proves that the constant-coefficient criterion is equivalent
   to membership in the extended ideal `p` plus the principal final-variable ideal.
   This gives both the ideal equality and the explicit membership equivalence.
   When `m = 0` the shear exponent family is empty and `B` is the field itself.
-/
theorem exists_monic_prime_coordinate_chart
    (k : Type u) [Field k] (m : ℕ)
    (q : Ideal (MvPolynomial (Fin (m + 1)) k)) [q.IsPrime] (hq : q ≠ ⊥)
    (g : MvPolynomial (Fin (m + 1)) k) (hg : g ≠ 0) (hgq : g ∈ q) :
    ∃ (e : Fin m → ℕ) (a : k) (d : ℕ)
      (sigma : MvPolynomial (Fin (m + 1)) k ≃ₐ[k] MvPolynomial (Fin (m + 1)) k)
      (f : MvPolynomial (Fin (m + 1)) k)
      (F : Polynomial (MvPolynomial (Fin m) k))
      (qStar : Ideal (MvPolynomial (Fin (m + 1)) k))
      (psi : Polynomial (MvPolynomial (Fin m) k) →ₐ[k] MvPolynomial (Fin (m + 1)) k)
      (p : Ideal (MvPolynomial (Fin m) k)),
      (∀ i : Fin m, 0 < e i) ∧ a ≠ 0 ∧ 0 < d ∧
      (∀ i : Fin m, sigma (MvPolynomial.X i.castSucc) =
        MvPolynomial.X i.castSucc + MvPolynomial.X (Fin.last m) ^ e i) ∧
      sigma (MvPolynomial.X (Fin.last m)) = MvPolynomial.X (Fin.last m) ∧
      (∀ i : Fin m, sigma.symm (MvPolynomial.X i.castSucc) =
        MvPolynomial.X i.castSucc - MvPolynomial.X (Fin.last m) ^ e i) ∧
      sigma.symm (MvPolynomial.X (Fin.last m)) = MvPolynomial.X (Fin.last m) ∧
      f = MvPolynomial.C a⁻¹ * sigma g ∧
      F.Monic ∧ F.natDegree = d ∧
      Polynomial.aevalTower (MvPolynomial.rename Fin.castSucc)
        (MvPolynomial.X (Fin.last m)) F = f ∧
      qStar = Ideal.map sigma.toRingHom q ∧ qStar.IsPrime ∧ f ∈ qStar ∧
      psi = Polynomial.aevalTower (MvPolynomial.rename Fin.castSucc) f ∧
      psi.toRingHom.Finite ∧
      (∀ h : MvPolynomial (Fin (m + 1)) k,
        ∃ c : Fin d → Polynomial (MvPolynomial (Fin m) k),
          h = ∑ j : Fin d, psi (c j) * MvPolynomial.X (Fin.last m) ^ (j : ℕ)) ∧
      p = Ideal.comap (MvPolynomial.rename Fin.castSucc).toRingHom qStar ∧ p.IsPrime ∧
      Ideal.comap psi.toRingHom qStar =
        Ideal.map Polynomial.C p ⊔ Ideal.span {Polynomial.X} ∧
      (∀ H : Polynomial (MvPolynomial (Fin m) k),
        psi H ∈ qStar ↔ Polynomial.eval 0 H ∈ p) := by
  sorry

end Algebra
