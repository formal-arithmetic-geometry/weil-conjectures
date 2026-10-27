## What changed

The item module now proves the scalar realization isomorphism by assembling the
coherent finite quotient extension model and a universal left-derived comparison
between its scalar functor and `integralComparisonDerivedSequenceScalar`. The
original theorem packages this realization together with a single split-off
normalization theorem. Added proof-only imports for
`CoefficientExtensionReductionModel` and `TransportedReductionScalarNormalized`.

## Proved and sorry left

The realization theorem `primitiveQuotientScalarModelRealization` is proved, and
the original `primitiveQuotientScalarModelExistence` is proved from it and the
normalization interface. One strictly smaller hole remains:
`primitiveQuotientScalarModelNormalization`, represented by
`lem-trf-primitive-quotient-scalar-model-normalization`. No definition contains
`sorry`.

## No longer needed

The original broad proof plan's direct dependencies on the flat resolution,
K-flat change-of-rings, finite inverse-image exactness, countable-product
exactness, strict Roos comparison, tensor descent, and flat Roos descent are not
used directly by this module. They are encapsulated by the existing coherent
extension reduction model. The proof uses only the coefficient evaluation
calculus, semilinear derived sections, the sequence scalar-map definitions,
the coherent extension reduction model, and the derived-change-of-rings model.

## Where the brief, the DAG or earlier work was wrong

The original node treated realization construction and quotient-generator
normalization as one indivisible step. The realization can be assembled from the
existing coherent extension reduction model and left-derived uniqueness; the
remaining normalization is a separate, strictly smaller statement. The item node
and new node record this decomposition.

## New nodes

`lem-trf-primitive-quotient-scalar-model-normalization`: normalization of the
constructed realization on every coherent quotient presentation. Its declaration
is in the item module and its proof remains `sorry` for a later worker.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
