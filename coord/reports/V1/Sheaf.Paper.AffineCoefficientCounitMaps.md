## What changed

Filled the sole proof hole in `Sheaf.Paper.AffineCoefficientCounitMaps`.
`AlgebraicGeometry.ProEtale.AffineCoefficientCounit.modulusUnit` now takes
`AffineLinePurity.primeUnit P Y aY`, raises it to `r + 1` using Mathlib's
`IsUnit.pow`, and rewrites the natural-number cast with `Nat.cast_pow`.
This implements the existing docstring proof without changing the route,
statements, definitions, public imports, or DAG attachments.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.AffineCoefficientCounit.modulusUnit`
(node `def-pur-affine-coefficient-counit-coordinate-maps`).
No holes remain in the item; no holes were added or split off.
The proof uses the existing `AffineLinePurity.primeUnit` theorem, whose
own proof remains an existing downstream obligation in
`Sheaf.Paper.AffineLinePurityComparison`; it is not claimed closed here.
The argument works for `r = 0` and for the empty scheme without extra hypotheses.

## No longer needed

None. No imports were added or removed. The existing public imports support
this module's definitions and signatures. No planned dependency, module,
node, or unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring already describes the direct proof.
LeanFinder and Loogle confirmed Mathlib's `IsUnit.pow`; source search confirmed
`Nat.cast_pow` and the exact existing signature of `AffineLinePurity.primeUnit`.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
