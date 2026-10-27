## What changed

The target theorem now reduces to two strictly simpler named intermediate theorems: the exactness of the concrete coefficient functor and the normalized finite quotient comparison. The target module imports these proof-only modules and combines their results. The intermediate theorem proofs remain `sorry` for parallel completion.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientRealization` is proved from the two split statements. Two sorries were added, one each in `completedKoszulFiniteQuotientComparison` and `completedKoszulFiniteQuotientExactness`, with nodes `new-s3-completed-koszul-finite-quotient-comparison` and `new-s3-completed-koszul-finite-quotient-exactness`.

## No longer needed

No declared proof dependency was removed; the target uses the finite quotient comparison and exactness split modules.

## Where the brief, the DAG or earlier work was wrong

The original node bundled exactness and the finite quotient normalization into one large theorem. The implementation isolates these independent steps so each can be proved directly from the existing coefficient and reconstruction declarations.

## New nodes

`new-s3-completed-koszul-finite-quotient-comparison` and `new-s3-completed-koszul-finite-quotient-exactness` are added under `dag/nodes/sec-proper-base-change/`.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
