## What changed

Filled `AddSubmonoid.saturated_fractional_column_descent` without changing its
signature or public imports. A proved private helper clears the positive common
denominator and applies NSMul saturation. The determinant identity uses
`Matrix.det_updateCol_sum` and `Int.cast_det`; the remaining assertions follow
from positivity and multiplication of the coefficient bound. Added only private
proof imports for submonoid finite sums and positivity of finite products.
The proof has been checked by the required server single-file compiler; delivery
preflight repeats the compile and axiom checks.

## Proved and sorry left

Closed the one original hole:
`AddSubmonoid.saturated_fractional_column_descent`
(node `lem-trf-saturated-monoid-fractional-column-descent`).
No holes remain and no holes were added. No split-off statements.

## No longer needed

No original imports or library modules were removed. The proof does not need a
separate invocation of `lem-weil-pbc-det-repeated-column-zero`: the proved
Mathlib theorem `Matrix.det_updateCol_sum` contains that calculation already.
Removed this direct proof dependency from the item node; it remains a Mathlib
leaf available to its other users. No unit statements or steps were bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The node's explicit Leibniz expansion
can be replaced by the existing Mathlib column replacement theorem. The
common-denominator construction also works with an empty index type or zero
coefficients; positivity of the replacement coefficient is used only for the
strict determinant assertions. Negative original determinants are handled by
`abs_mul`.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
