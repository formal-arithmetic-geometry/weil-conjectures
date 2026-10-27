module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# A triangular coordinate change regular on the last axis

Source: EGA IV4, proof of Theorem 21.14.1, reduction of the complete power-series case
to one variable; Bourbaki, Algebre commutative VII, section 3, no. 7, Lemma 3
(blueprint: lem-sfb-power-series-axis-coordinate-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPowerSeries

/-- A nonzero reduced series becomes nonzero on the last coordinate axis after a
triangular substitution. Source: EGA IV4, proof of Theorem 21.14.1, one-variable reduction,
and the cited Bourbaki VII, section 3, no. 7, Lemma 3
(blueprint: lem-sfb-power-series-axis-coordinate-change).

The dimension is `n + 1`; `Fin.last n` indexes the last variable, and `i.castSucc`
indexes the preceding variables. Both equalities quantify over every input series:
`subst` is Mathlib's coefficientwise summation with discrete coefficients, so these
specify the formal substitutions themselves. Their entries have zero constant
coefficient, and finitely many variables ensure `HasSubst`; no dummy evaluation occurs.
The final `subst` sets all preceding variables to zero and the last to `PowerSeries.X`.

Proof:
1. In the nonempty support of the coefficientwise reduction, successively minimize
   the first exponent, then the second among those already selected, and so on. This
   gives an exponent alpha. Set the last weight to 1, and recursively set each earlier
   weight to 2 plus the sum of the later weights times the corresponding alpha entries.
   If beta differs from alpha first at j, the weighted difference is at least the j-th
   weight minus the later weighted alpha entries, hence strictly positive. Thus alpha
   is the unique supported exponent of minimal weight; the earlier weights are at least 2.
2. Use `lem-weil-pbc-power-series-variables-complete` for the variables ideal J and
   `lem-weil-pbc-power-series-adic-evaluation` for the two tuples X_i plus or minus the
   indicated powers of the last variable. All entries belong to J. The unique continuous
   ring maps fix constants, so are A-algebra maps. Their truncation formulas are precisely
   coefficientwise substitution, using `def-weil-pbc-multivariate-power-series`.
3. The two composites fix every variable because the last variable is fixed and the
   corrections cancel. Uniqueness in `lem-weil-pbc-power-series-adic-evaluation` identifies
   both composites with the identity. For n = 0 the original tuples already are the
   identity tuple, giving the stated identity automorphism.
4. Reduce coefficients and restrict to the last axis. This map sends J^N into (t)^N.
   Its composite with the positive substitution has the same constants and variables as
   evaluation at the selected powers of t; the same uniqueness theorem identifies them.
   By its truncation formula, the coefficient of t^N is the sum of the reduced input
   coefficients whose weighted degree is N. This sum is finite since all weights are
   positive, so all contributing monomials have ordinary total degree at most N.
5. At the weighted degree of alpha, exactly its nonzero coefficient survives by step 1.
   This proves axis nonvanishing over finite and imperfect residue fields as well. -/
theorem exists_triangular_axis_coordinate_change
    {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) A)
    (hf : MvPowerSeries.map (Ideal.Quotient.mk m) f ≠ 0) :
    ∃ e : Fin n → ℕ, (∀ i : Fin n, 2 ≤ e i) ∧
      ∃ σ : MvPowerSeries (Fin (n + 1)) A ≃ₐ[A] MvPowerSeries (Fin (n + 1)) A,
        (∀ g : MvPowerSeries (Fin (n + 1)) A,
          σ g = MvPowerSeries.subst
            (Fin.lastCases (MvPowerSeries.X (Fin.last n))
              (fun i : Fin n => MvPowerSeries.X i.castSucc +
                MvPowerSeries.X (Fin.last n) ^ e i)) g) ∧
        (∀ g : MvPowerSeries (Fin (n + 1)) A,
          σ.symm g = MvPowerSeries.subst
            (Fin.lastCases (MvPowerSeries.X (Fin.last n))
              (fun i : Fin n => MvPowerSeries.X i.castSucc -
                MvPowerSeries.X (Fin.last n) ^ e i)) g) ∧
        MvPowerSeries.subst
          (fun i : Fin (n + 1) =>
            if i = Fin.last n then (PowerSeries.X : PowerSeries (A ⧸ m)) else 0)
          (MvPowerSeries.map (Ideal.Quotient.mk m) (σ f)) ≠ 0 ∧
        (n = 0 → σ = AlgEquiv.refl) := by
  sorry

end MvPowerSeries
