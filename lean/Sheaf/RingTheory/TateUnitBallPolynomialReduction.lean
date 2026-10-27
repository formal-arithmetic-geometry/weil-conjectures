module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coefficient reduction of the Tate Gauss unit ball

Source: Bosch, Lectures on Formal and Rigid Geometry (April 2008), Section 1.2,
printed p. 9, the reduction paragraph before Proposition 3
(blueprint: lem-trf-tate-unit-ball-polynomial-reduction).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- Coefficient reduction of the restricted-series unit ball is a surjective unital ring
homomorphism to residue polynomials, with kernel the open Gauss unit ball.
Source: Bosch, Section 1.2, printed p. 9, before Proposition 3
(blueprint: lem-trf-tate-unit-ball-polynomial-reduction).

The subrings and ideal are specified by their exact carriers. Each coefficient of a unit-ball
series has a representative `a : V` equal to that coefficient, and its reduced polynomial
coefficient is the class of `a`. Thus the existential ring map is the specified coefficient map.
The predicate `IsField` concerns the quotient's existing ring structure.

Proof: (1) The ultrametric and multiplicative inequalities make the closed coefficient ball
`V` a unital subring and the open coefficient ball `m` a proper ideal of `V`.
(2) Every element of `V` outside `m` has norm one; its inverse also has norm one and lies in `V`.
No element of `m` is a unit. Therefore `V` is local with maximal ideal `m`.
(3) The quotient map has kernel `m`; inverses of representatives outside `m` show that the
quotient is a field. These use def-weil-field and def-weil-pbc-algebra-hom-quotient.
(4) Restrictedness makes the set of coefficients of norm at least any positive epsilon finite.
Taking epsilon one bounds all coefficients. Hence Gauss norm at most one is equivalent to
all coefficient norms being at most one.
(5) Coefficientwise addition and negation preserve this bound. Every product coefficient is
a finite Cauchy sum with summands of norm at most one, so the ultrametric inequality proves
closure under multiplication. This gives `U`, using def-trf-restricted-series-presentation.
(6) A nonzero residue coefficient must have norm one. Only finitely many coefficients do,
so their reductions define a polynomial, using def-weil-pbc-mv-polynomial-ring.
(7) Coefficientwise addition and finite Cauchy products commute with the residue map, as do
zero and one. Thus reduction is a unital ring homomorphism.
(8) Lift the finitely many coefficients of a polynomial to `V`; the resulting finite series
belongs to `U` and reduces to that polynomial. Constant series reduce to constant polynomials.
(9) Reduction vanishes exactly when all coefficient norms are less than one. Finitely many
are at least one half; their maximum together with one half is strictly below one and bounds
all coefficients. This is equivalent to Gauss norm less than one and proves the kernel claim.
(10) All coefficient sums are finite and all bounds use only restrictedness, not completeness.
With zero variables there is one multi-index; with a trivial norm restrictedness forces finite
support. Thus both edge cases are included. -/
theorem tateUnitBallPolynomialReduction (K : Type u) [NormedField K]
    [IsUltrametricDist K] (r : ℕ) :
    ∃ V : Subring K,
      (∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1) ∧ IsLocalRing V ∧
      ∃ m : Ideal V,
        (∀ a : V, a ∈ m ↔ ‖(a : K)‖ < 1) ∧ m.IsMaximal ∧ IsField (V ⧸ m) ∧
        ∃ U : Subring (MvPowerSeries.IsRestricted.subring
            (R := K) (fun _ : Fin r ↦ (1 : ℝ))),
          (∀ f : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ)),
            f ∈ U ↔ MvPowerSeries.gaussNorm (norm : K → ℝ)
              (fun _ : Fin r ↦ 1) f.val ≤ 1) ∧
          ∃ red : U →+* MvPolynomial (Fin r) (V ⧸ m),
            Function.Surjective red ∧
            (∀ (f : U) (ν : Fin r →₀ ℕ), ∃ a : V,
              (a : K) = MvPowerSeries.coeff ν f.val.val ∧
              MvPolynomial.coeff ν (red f) = Ideal.Quotient.mk m a) ∧
            (∀ f : U, f ∈ RingHom.ker red ↔
              MvPowerSeries.gaussNorm (norm : K → ℝ)
                (fun _ : Fin r ↦ 1) f.val.val < 1) ∧
            (∀ a : V, ∃ f : U,
              f.val = constants K r (a : K) ∧
              red f = MvPolynomial.C (Ideal.Quotient.mk m a)) := by
  sorry

end RestrictedSeries
