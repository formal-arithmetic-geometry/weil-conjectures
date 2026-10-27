module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdjoinRoot

/-!
# Integral closure of finite-variable Tate algebras

Source: Kedlaya, Tate algebras (2004), Proposition 5, p. 5, integrally-closed consequence;
Stacks Project, Tag 0AFV, denominator-prime argument
(blueprint: lem-trf-tate-integrally-closed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- A Tate algebra in finitely many variables is an integrally closed domain, including
zero variables. Source: Kedlaya, Tate algebras (2004), Proposition 5, p. 5;
Stacks Project, Tag 0AFV (blueprint: lem-trf-tate-integrally-closed).

Proof plan:
1. The genuine Gauss norm of lem-trf-restricted-series-gauss-completion and its
   multiplicativity in lem-trf-tate-gauss-multiplicative give nontriviality and no zero
   divisors. Induct on the number of variables to prove integral closure, in the sense
   of def-weil-pbc-normal-ring. At zero variables the restricted-series ring is K.
2. In positive dimension put A = D_(n-1) and D = D_n. Group coefficients by the final
   variable using lem-trf-restricted-series-gauss-completion. For nonzero f,
   lem-per-tate-triangular-distinguished-coordinate gives an isometric automorphism sigma
   and a unit v in A such that g = v sigma(f) is normalized distinguished of degree d.
   Apply lem-trf-tate-weierstrass-norm-division to write g = u w, with u a unit and w a
   monic polynomial of degree d whose lower coefficients have norm at most one.
   When d = 0 this polynomial is one, so f is a unit.
3. By lem-sfb-normal-domain-monic-prime-factorization over the inductively normal A,
   factor w into finitely many monic positive-degree h_j with A[X]/(h_j) nonzero domains.
   Each factor and its monic complementary product have Gauss norm at least one.
   Multiplicativity and the norm-one condition on w force both norms to equal one.
   Therefore the lower coefficients of each h_j have norm at most one. Each h_j
   satisfies the division hypotheses, with zero upper tail. The empty product covers w = 1.
4. The polynomial inclusion induces A[X]/(h_j) -> D/(h_j), using
   def-weil-pbc-algebra-hom-quotient. Division proves surjectivity. For injectivity,
   lem-weil-pbc-monic-quotient-free gives a representative r of degree below deg(h_j).
   If r = q h_j in D, uniqueness of division applied to 0 h_j + r and q h_j + 0
   forces r = 0. Thus this comparison is a ring isomorphism.
5. The quotient D/(h_j) is a nonzero domain, so h_j is a prime element: its leading
   coefficient makes it nonzero, its nonzero quotient makes it a nonunit, and the
   domain property of the quotient gives the prime-product implication. The quotient
   kernel identifies vanishing with divisibility. Transporting by sigma inverse
   preserves primality. Undoing the normalization in step 2 therefore factors every
   nonzero f into a unit times finitely many prime elements of D.
6. Let z = a/b in the fraction field satisfy a monic equation of degree m. Necessarily
   m > 0 since the monic constant polynomial is one. Factor b as a unit times primes.
   Clearing denominators gives a^m + sum_(i<m) c_i a^i b^(m-i) = 0 in D, by injectivity
   of its fraction-field map. Any prime p dividing b divides every summand of the sum,
   hence divides a^m. Repeated use of the prime-product property gives p dividing a.
   Cancel p from a and b in the fraction field, obtaining the same integral element
   with one fewer prime in the denominator.
7. Induction on the finite number of denominator primes ends with a unit denominator,
   so z is in D. This proves integral closure and finishes the dimension induction.
   Completeness and nontriviality are exactly those of the stated field hypotheses. -/
theorem tate_isDomain_and_isIntegrallyClosed
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (d : ℕ) :
    IsDomain (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) ∧
      IsIntegrallyClosed
        (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))) := by
  sorry

end RestrictedSeries
