## What changed

Replaced the sole `sorry` in
`lean/Sheaf/DeligneLaumon/RationalSeriesPoleRadius.lean` with a complete proof of
`PowerSeries.radius_le_of_polynomial_mul_eq`, following the existing node
`lem-wf-rational-series-pole-radius` and its source's final Taylor-radius argument.
The declaration, docstrings, imports, definitions, and dependency route are unchanged.

Assuming the radius exceeds the root modulus, the existing
`PowerSeries.summable_norm_coeff_mul_pow` gives absolute convergence at that root.
The polynomial coefficient series is finitely supported. Mathlib's
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` evaluates their Cauchy
product. The coefficient identity `Q * f = P` identifies its sum with `P.eval a`,
whereas `Q.eval a = 0` makes it zero, contradicting `haP`.
The coefficient calculation follows the already proved inverse-polynomial case in
`WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`.

LeanFinder and Loogle found no theorem directly proving the requested statement;
local searches located that inverse-polynomial proof and Mathlib's Cauchy-product
identity. No new API, node, or statement repair was necessary.

## Proved and sorry left

Closed 1 of 1 holes: `PowerSeries.radius_le_of_polynomial_mul_eq`
(node `lem-wf-rational-series-pole-radius`). Added 0 holes; split off 0 statements.
There are no remaining `sorry`s in the delivered module.

## No longer needed

None. Both existing public imports support the statement and proof, and all five
existing node dependencies remain used. No imports, nodes, or modules were removed.

## Where the brief, the DAG or earlier work was wrong

No discrepancy. The original nonzero-constant-coefficient hypothesis is unnecessary
for this direct contradiction, but is retained unchanged and explicitly referenced
in the proof to satisfy the unused-variable linter. The proof never divides by `a`, `Q`, or a coefficient, so zero-root
and constant-polynomial cases require no extra hypotheses. A common numerator and
denominator root remains excluded exactly by the existing `haP` hypothesis.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
