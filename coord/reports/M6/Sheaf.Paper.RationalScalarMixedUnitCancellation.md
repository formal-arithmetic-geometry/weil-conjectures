## What changed

Prove AlgebraicGeometry.Scheme.rationalMixedRawCoefficientTower in the assigned
module, using the published coefficient-tower equation of
rationalScalarCompletionUnitSquare_coefficients. Four proved private helpers
supply the denominator-one scalar and raw pullback map formulas, a general
inversion identity for a commuting square, and the strict beta coefficient-tower law. The latter follows by inverting the reflected law,
conjugating through the specified ambient quotient comparisons, and cancelling
inverse pairs by naturality. The public proof retains all raw-object transports
and applies rationalization to this strict integral equation.

Update the owning node's final proof step and proof-origin description to record
this argument. Existing signatures, data, attributes and public imports are preserved.

Validation: lcompile.py compiled the complete module without errors or warnings
in 59.8 seconds, within the 60-second file limit. Profiling options were removed
before that successful compile. The delivery tool performs the required
preflight and declaration/axiom checks.

## Proved and sorry left

Original holes: 7. Closed: 1. Added: 0. Split off: 0.

Closed: AlgebraicGeometry.Scheme.rationalMixedRawCoefficientTower.

The following six original holes remain, all attached to
lem-per-rational-scalar-mixed-unit-cancellation, in namespace
AlgebraicGeometry.Scheme:

- rationalScalarMixedUnitCancellation
- rationalMixedGeometricComposition
- rationalMixedRawGeometricComposition
- rationalMixedGeometricIdentity
- rationalMixedCoefficientTower
- rationalMixedCoefficientIdentity

## No longer needed

No existing imports, modules or nodes are removed. The raw coefficient-tower
proof needs neither a new K-flat representative calculation nor the derived zeta
tower theorem: the existing reflected coefficient-tower law suffices. The other
six original obligations retain their existing dependency plan and unit route.

## Where the brief, the DAG or earlier work was wrong

The raw coefficient-tower companion admits a direct categorical proof from the
specified integral coefficient-tower comparison. It does not require reconstructing
the ordinary tensor comparison on representatives or assuming a new coherence law.
The rework row mentions quarantine after a transitive false-tail import; the current
assigned module exists in the live source, and its Lean attachment and dependencies
are retained. No module is withdrawn.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
