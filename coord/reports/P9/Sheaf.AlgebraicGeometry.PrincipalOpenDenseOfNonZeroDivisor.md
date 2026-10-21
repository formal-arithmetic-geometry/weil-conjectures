## What changed

Filled `PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors` in
`Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor`, preserving its signature,
docstrings, and imports. The proof follows the existing DAG plan: identify the principal
open with the localization's spectrum image, apply the minimal-prime density criterion,
and exclude the nonzerodivisor from each minimal prime. All three facts are already in
the publicly imported Mathlib module, so no additional imports are needed.

## Proved and sorry left

Closed the one hole in `PrimeSpectrum.dense_basicOpen_of_mem_nonZeroDivisors`
(node `lem-pc-principal-open-dense-of-nonzerodivisor`). Zero holes remain and zero
holes are added. There are no split-off statements.

Validation: the final module compiles cleanly through `lcompile.py` in 1.7 seconds.
An explicit `#print axioms` probe also compiles (1.8 seconds) and reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. No imports, nodes, or modules are pruned. The proof uses all three declared
proof dependencies through their existing Mathlib matches:
`lem-weil-pbc-spec-localization-away-basic-open`,
`lem-pc-dense-range-comap-minimal-primes`, and
`lem-pc-minimal-prime-avoids-nonzerodivisor`.

## Where the brief, the DAG or earlier work was wrong

No correction was needed. The statement and route are unchanged. In the zero ring the
prime spectrum is empty, and the minimal-prime criterion applies vacuously; no
nontriviality hypothesis is introduced. The argument also applies to units and to
nonzerodivisors in rings with several minimal primes.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
