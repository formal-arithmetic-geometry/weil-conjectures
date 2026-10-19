## What changed

Proved five declarations in `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle`.
The two closedness results use Mathlib's closed-immersion base-change instances; the
open-complement identity uses `Scheme.Pullback.range_snd`. The two derived comparison
theorems construct the canonical comparison with the right-derived composition
isomorphism and prove its unit normalization and uniqueness by the right-derived
universal property. Added the proof-only import `Mathlib.AlgebraicGeometry.PullbackCarrier`.

The module compiles with `lcompile.py`.

## Proved and sorry left

Closed five original holes:

- `supportIntersection_closed`
- `supportOnOpen_closed`
- `exists_unique_supportOpenDerivedComparison`
- `supportOnOpen_complement`
- `exists_unique_supportTransportComparison`

Eight original holes remain, unchanged:

- `exists_unique_supportInclusion`
- `exists_unique_supportOpenRestriction`
- `supportInclusion_restriction_zero`
- `supportLocalizationComplex_shortExact`
- `exists_unique_supportLocalizationBoundary`
- `normalizedSupportTriangle_distinguished`
- `exists_unique_supportTransport`
- `derivedSupportTransport_isIso`

No new `sorry` declarations were added and no definitions contain `sorry`.

## No longer needed

No imports or DAG nodes were pruned. The proof adds the proof-only import
`Mathlib.AlgebraicGeometry.PullbackCarrier`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not expose the direct Mathlib base-change and pullback-range
lemmas, nor the right-derived universal-property construction for the two comparison
theorems. Those routes close the corresponding holes without changing any statements or
unit-level route.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
