## Worker report

The module `Sheaf.DeligneLaumon.RationalSeriesPoleRadius` states
`PowerSeries.radius_le_of_polynomial_mul_eq`. It uses `Polynomial ℂ` for the two
polynomials, `PowerSeries ℂ` for the formal series, the coercion
`Polynomial.coeToPowerSeries` for the identity in `ℂ⟦X⟧`, `Polynomial.coeff 0`
for the nonzero constant term, `Polynomial.eval` for evaluation at `a`, and
`PowerSeries.radius` with `ENNReal.ofReal ‖a‖` for the radius bound.

The hypotheses and conclusion render the node as follows:

* `P,Q ∈ ℂ[T]` are `(P Q : Polynomial ℂ)`.
* `f ∈ ℂ[[T]]` is `(f : PowerSeries ℂ)`.
* The denominator condition `Q(0) ≠ 0` is `hQ0 : Q.coeff 0 ≠ 0`.
* The formal identity `Qf = P` in `ℂ[[T]]` is
  `hQf : (Q : PowerSeries ℂ) * f = (P : PowerSeries ℂ)`.
* For `a ∈ ℂ`, `Q(a)=0` and `P(a)≠0` are
  `haQ : Q.eval a = 0` and `haP : P.eval a ≠ 0`.
* The conclusion `R(f) ≤ |a|` is
  `f.radius ≤ ENNReal.ofReal ‖a‖`; the norm is the complex absolute value.

Dependency declarations used:

* `def-weil-polynomial-ring`: Mathlib `Polynomial` in
  `Mathlib.Algebra.Polynomial.Basic` (the recorded `Polynomial` declaration).
* `def-weil-formal-power-series`: Mathlib `PowerSeries` (the recorded
  `mathlib_match`).
* `def-weil-polynomial-as-power-series`: Mathlib coercion and ring hom
  `Polynomial.coeToPowerSeries.ringHom` in
  `Mathlib.RingTheory.PowerSeries.Basic`.
* `d-real-series`: `PowerSeries.radius` in
  `WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`.
* `def-weil-complex-absolute-value`: the `Complex.instNorm` norm, used as
  `‖a‖`.

Edge cases checked: `Q` may be constant (then `Q.eval a = 0` is impossible when
`Q(0) ≠ 0`), `P` may be zero (then `P.eval a ≠ 0` is impossible), `a = 0` is
excluded by the conjunction `Q(0) = 0` versus `Q(0) ≠ 0`, and the zero series
causes no issue because the hypotheses cannot hold with `P.eval a ≠ 0`. The
radius is allowed to be `0` or `∞` through the `ENNReal` definition.

Searches made:

* `msearch.py ... leanfinder "polynomial times formal power series equals polynomial denominator root convergence radius"`: eight hits, all general radius or analytic-series declarations; no exact match.
* `msearch.py ... loogle "PowerSeries.radius, Polynomial.eval"`: zero hits (service reported unknown `PowerSeries.radius`).
* `msearch.py ... grep "radius.*pole" Mathlib/Analysis`: zero hits.
* `rg` over `WeilConjectures/` and the project `lean/Sheaf/` for
  `radius.*pole`, `rational.*series.*radius`, and the declaration name: no
  existing theorem.

No statement correction, new definition node, or dependency repair was needed.

## Second reading by Q137

I reread the node and the source paragraph. The Lean binders preserve every
hypothesis and clause: both polynomials are over `ℂ`, the series is a formal
power series, the polynomial identity is interpreted through the canonical
coercion, `Q(0) ≠ 0` is retained, and the root and non-cancellation conditions
are separate hypotheses. The conclusion uses the existing `PowerSeries.radius`
and the complex norm. I also reread all five dependency records and their
recorded declarations; no record was unusable and no existing theorem states
this polynomial-times-series radius obstruction.
