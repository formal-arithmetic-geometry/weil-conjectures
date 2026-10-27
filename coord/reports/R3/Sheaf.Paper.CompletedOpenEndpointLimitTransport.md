## What changed

Filled the six original theorem holes. Scalar/open invertibility follows from the
fully faithful open adjunctions and the ringed scalar comparison, which places its
output in the essential image of the constant open extension. Reduction invertibility
uses the strict ringed reduction isomorphism in the same way, after canonical
left-adjoint transport. Exact localization preserves the invertible open units.
Naturality is inverse-mate naturality.

The direct normalized Roos comparison is identified with the specified derived
constant-diagram mate. Product preservation gives its invertibility for scalar
restriction and both open extensions. Exact-derived and mate cubes give the limit
square. Transposition proves quotient augmentation, and cancellation and naturality
prove the two final endpoint identities.

Only proved private helpers and private proof imports were added. Existing signatures,
definitions, public imports and visibility are retained. The existing node's proof,
proof dependencies and proof origin follow the final argument. No other library
module is changed.

## Proved and sorry left

Closed six of six original holes:

- `AlgebraicGeometry.Scheme.cbcEndpointScalarOpenInv_isIso`
- `AlgebraicGeometry.Scheme.cbcEndpointReductionInv_properties`
- `AlgebraicGeometry.Scheme.cbcEndpointScalarLimit_properties`
- `AlgebraicGeometry.Scheme.cbcEndpointOpenLimit_properties`
- `AlgebraicGeometry.Scheme.cbcEndpointReduction_augmentation`
- `AlgebraicGeometry.Scheme.completedOpenEndpointLimitTransport`

All belong to `lem-cbc-completed-open-endpoint-limit-transport`.
Zero remaining holes; zero added holes; zero statements split off.

## No longer needed

No existing public import, node, module or declaration is withdrawn.
CompleteProetaleStrictTowerRealization is not imported: its updated reduction proof
uses this item, so transporting that result back would be circular. The direct
ringed strict reduction theorem replaces that route. Its generic limit-invertibility
theorem is also not used. The direct normalized Roos argument uses
ExactEquivalenceDerivedSquares, StrictRoosShiftLocalization,
NormalizedLimitSquareCoherence, ExactProductFunctorStrictLimit and strict mate
normalization. RingedOpenScalarLimitCoherence remains needed for its normalized
comparison equation and countable-product helper. The broad
UnboundedExactAdjunctionSquare proof import is replaced by the two cube modules.
SemilinearEvaluationDerivedAdjunction is not imported; its generic proved
adjunction-identification argument is reproduced privately using narrow imports.

## Where the brief, the DAG or earlier work was wrong

The original plan described normalized limit identification without a ready-to-apply
formula for the actual endpoint functors; the proof supplies that formula directly.
During this session the realization module was updated to import this endpoint module
and prove reduction invertibility from it. The initially available interface transport
route consequently became circular. The final proof avoids the realization module
entirely and obtains the essential-image witness from ringed strict reduction.
No mathematical statement was changed or disputed. The unit route is retained.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
