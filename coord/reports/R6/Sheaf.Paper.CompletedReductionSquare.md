## What changed

Saved a proof of `AdicCoefficientDatum.completionDirectImageComparison_isIso` by unfolding
its ordered composite and using the existing `towerProjection_isIso` instance, preservation
of isomorphisms by derived limit, and the two specified comparison isomorphisms.
No delivery has been attempted. Compiler validation is pending: the first lcompile call
returned exit 124, "no answer from the compile server within 202 s (server busy or
unreachable)". A second item compile also returned exit 124 after 194 s with the same no-answer diagnostic.
A small independent compile-service probe succeeded in 1.2 s, so a third item compile
also returned exit 124 after 194 s with the same no-answer diagnostic. All three item
compile calls have finished. This is a compile-service response failure, not a Lean
60-second per-file timeout. No delivery was run. The module and this recovery report
remain in the original sandbox for resumption.

## Proved and sorry left

One of the three original holes has a proof written, pending compiler validation:
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completionDirectImageComparison_isIso`.
Two original holes remain, both attached to
`def-weil-pbc-completed-reduction-square`:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedDirectImageReduction_isIso`
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedReductionSigma_isIso`

No holes added. No completed proof count is claimed before compilation.

## No longer needed

No imports removed yet. No pruning claimed.

## Where the brief, the DAG or earlier work was wrong

The owning node is a definition with empty `proof` and `proof_deps`; its three postponed
invertibility assertions have their argument in the Lean docstrings and statement
dependencies. The direct-image assertion already follows from
`AdicCoefficientDatum.towerProjection_isIso` in `CompletedDirectImageLimits`.
The remaining arbitrary-input rho assertion needs more than applying
`finiteReductionReconstructionCompleted`, whose input explicitly requires intrinsic
completeness. `completedPullback_reduction` also requires complete input and uses a
differently normalized presentation, so comparison of the specified maps is required.
`CompletedPullbackUnitTower.completedPullbackUnitTower` supplies arbitrary-input reduction
of the completion unit in constant coefficients, on transported small sites; applying it
requires the completed-coefficient and normalization comparisons, not definitional equality.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
