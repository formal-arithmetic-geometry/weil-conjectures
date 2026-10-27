module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Weierstrass division and preparation with Gauss norm bounds

Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, norm-controlled
Weierstrass division and preparation for strictly convergent series
(blueprint: lem-trf-tate-weierstrass-norm-division).
The book is not available locally; the DAG supplies an agent-written proof,
without claiming a verified theorem number.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- The coefficient of the distinguished variable in a multivariate series.
We index that variable by `0` and the other variables by `Fin.succ`.
Source: the coefficient regrouping in the norm-controlled Weierstrass division statement
(blueprint: lem-trf-tate-weierstrass-norm-division). -/
noncomputable def weierstrassCoefficient
    {F : Type u} [CommRing F] {s : ℕ}
    (g : MvPowerSeries (Fin (s + 1)) F) (i : ℕ) : MvPowerSeries (Fin s) F :=
  PowerSeries.coeff i (MvPowerSeries.finSuccEquiv F s g)

/-- The canonical inclusion of a polynomial over restricted series into formal series
in one more variable, using Mathlib's coefficient inclusion and regrouping equivalence.
Source: the inclusion of `A[X]` into `D` in norm-controlled Weierstrass division
(blueprint: lem-trf-tate-weierstrass-norm-division). -/
noncomputable def weierstrassPolynomialExpansion
    {F : Type u} [NormedField F] [IsUltrametricDist F] {s : ℕ}
    (r : Polynomial (MvPowerSeries.IsRestricted.subring
      (R := F) (fun _ : Fin s ↦ (1 : ℝ)))) : MvPowerSeries (Fin (s + 1)) F :=
  (MvPowerSeries.finSuccEquiv F s).symm
    (Polynomial.map (MvPowerSeries.IsRestricted.subring
      (R := F) (fun _ : Fin s ↦ (1 : ℝ))).subtype r)

/-- Norm-controlled analytic Weierstrass division and preparation.
Source: Bosch--Güntzer--Remmert, Non-Archimedean Analysis, Weierstrass division
and preparation for strictly convergent series; the book is WANTED locally
(blueprint: lem-trf-tate-weierstrass-norm-division).

Proof (the DAG's agent reconstruction):
1. Apply lem-trf-restricted-series-gauss-completion to the coefficient algebra and the
   algebra with the distinguished variable. The remainder space is the complete finite
   product of `d` coefficient algebras. Split `g = p + e`, with `p` monic of degree `d`
   and `c = ‖e‖ < 1`.
2. Divide polynomials by `p` by descending degree: cancel the leading term and use the
   ultrametric inequality to preserve both norm bounds. Monicity proves uniqueness,
   and then additivity and coefficient linearity of the quotient and remainder operators.
3. Extend these operators to restricted series by limits of distinguished-variable
   truncations, using completeness. Their bounds, decomposition identity, and inverse
   identity on `pv + t` pass to the limit.
4. Starting with `h₀ = h`, take `vⱼ = Q₀(hⱼ)`, `tⱼ = R₀(hⱼ)` and `hⱼ₊₁ = -evⱼ`.
   The norms are bounded by `c^j ‖h‖`. Completeness and the ultrametric inequality give
   convergent sums `q` and `r`, both bounded by `‖h‖`. Sum the recursion and pass to
   the limit to get the division identity.
5. A difference `gv + t = 0` gives `v = -Q₀(ev)`, hence `‖v‖ ≤ c ‖v‖`, so `v = t = 0`.
   This proves uniqueness without assuming bounds on competing decompositions.
6. Divide `X^d = bg + r`. Then `‖1-b‖ ≤ c < 1`; geometric sums explicitly construct
   its inverse `u` with norm at most one. Set `w = X^d-r`, obtaining `g = uw`, and
   `‖u⁻¹‖ = ‖b‖ ≤ 1`. The coefficient bounds follow from those on the remainder.
7. If `d = 0`, the remainder space is zero and `w = 1`. If `h = 0`, every correction
   term is zero. The empty list of coefficient variables and a zero upper tail are
   included in the same construction. -/
theorem tate_weierstrass_norm_division
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (s d : ℕ)
    (g : MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin (s + 1) ↦ (1 : ℝ)))
    (hd : weierstrassCoefficient g.val d = 1)
    (hlower : ∀ i : ℕ, i < d →
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin s ↦ 1)
        (weierstrassCoefficient g.val i) ≤ 1)
    (hupper : (⨆ i : {i : ℕ // d < i},
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin s ↦ 1)
        (weierstrassCoefficient g.val i.val)) < 1) :
    (∀ h : MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin (s + 1) ↦ (1 : ℝ)),
      ∃ (q : MvPowerSeries.IsRestricted.subring
          (R := F) (fun _ : Fin (s + 1) ↦ (1 : ℝ)))
        (r : Polynomial (MvPowerSeries.IsRestricted.subring
          (R := F) (fun _ : Fin s ↦ (1 : ℝ)))),
        r.degree < (d : WithBot ℕ) ∧
        h.val = q.val * g.val + weierstrassPolynomialExpansion r ∧
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1) q.val ≤
          MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1) h.val ∧
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1)
            (weierstrassPolynomialExpansion r) ≤
          MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1) h.val ∧
        (∀ (q' : MvPowerSeries.IsRestricted.subring
            (R := F) (fun _ : Fin (s + 1) ↦ (1 : ℝ)))
          (r' : Polynomial (MvPowerSeries.IsRestricted.subring
            (R := F) (fun _ : Fin s ↦ (1 : ℝ)))),
          r'.degree < (d : WithBot ℕ) →
          h.val = q'.val * g.val + weierstrassPolynomialExpansion r' → q' = q ∧ r' = r) ∧
        (d = 0 → r = 0)) ∧
    (∃ (w : Polynomial (MvPowerSeries.IsRestricted.subring
          (R := F) (fun _ : Fin s ↦ (1 : ℝ))))
        (unit : (MvPowerSeries.IsRestricted.subring
          (R := F) (fun _ : Fin (s + 1) ↦ (1 : ℝ)))ˣ),
      w.Monic ∧ w.natDegree = d ∧
      (∀ i : ℕ, i < d →
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin s ↦ 1) (w.coeff i).val ≤ 1) ∧
      g.val = unit.val.val * weierstrassPolynomialExpansion w ∧
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1) unit.val.val ≤ 1 ∧
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1)
        (unit⁻¹).val.val ≤ 1 ∧
      (d = 0 → w = 1)) := by
  sorry

end RestrictedSeries
