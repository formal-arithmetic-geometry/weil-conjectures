## What changed

Replaced the hole in `Sheaf.Paper.DiagonalTraceLimitWitnessExistence` with a reduction
through a single finite coefficient projection calculation. The completed integral
is between sheaves placed in degree zero. Full faithfulness represents it by an
ordinary sheaf endomorphism. The proved private helper
`coefficientProjection_jointly_monic` detects its identity on sections using the
actual inverse-limit presentation of the completed coefficient ring. The proof then
constructs the required witness with the identity tower endomorphism, the specified
tower and limit functor, and the invertible `unitMap`/single comparison.

Added `Sheaf.Paper.DiagonalTraceFiniteIntegralProjection`, containing only the
finite projection calculation. No existing statement, definition, instance,
attribute, or public import changes. No source-library files change.

Validation: both delivered modules compile cleanly through `lcompile.py` against
the server build. The original module compiled in 57.7 seconds, and the final
finite-projection module in 7.2 seconds. No transparency or time-limit overrides
were introduced.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_limitWitness_exists`.
Added one hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteIntegralProjection`,
node `lem-sfb-diagonal-trace-finite-integral-projection`.
The original module has zero remaining holes; the new module has one. This is a
one-to-one decomposition, not a net closure of the mathematical obligation.
The equality-detection helper and the entire assembly of the original theorem are
proved. The remaining theorem asserts one fixed finite exponent's projection
equation, without a tower endomorphism or a limit witness. It is strictly the
finite calculation step; the passage from these equations to the original whole
witness is implemented in Lean.

## No longer needed

No original imports removed: `DiagonalTraceSources` supplies the statement data,
and `SingleTowerEvaluationFaithful` supplies the witness structure in its signature.
The evaluation-faithfulness and limit-identity theorems of the latter module are
not used by the new proof, although its structure remains necessary.

The original node's direct proof dependencies are replaced by the finite-projection
node and the Mathlib degree-zero full-faithfulness leaf. Its original dependencies
`det-prop-diagonal-tower-system` and `det-prop-diagonal-tower-limit` assert existence
results not needed when `hδ` already supplies the full normalized limit data. Their
definitions remain available through the unchanged public imports. The finite
projection calculation still needs coefficient/direct-image evaluation comparison,
finite P1 integration, and compatibility of direct image with limit projections;
these remain dependencies of the new node. No existing module is withdrawn, and
no whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned construction of a new derived system composite is unnecessary for
this witness statement. The completed composite is already between degree-zero
sheaves. Ordinary inverse-limit detection after full faithfulness is enough, and
the witness can then use the identity system map. This never treats evaluation or
limit projections as faithful on arbitrary derived morphisms.

The finite normalization and comparison calculation remains substantial; it is
isolated with the exact finite coefficient-projection equation needed downstream.
Its source is paragraph (2) and expanded steps 9--10 of the trace proof. The
unit record's realized route is unchanged. Edge cases: n=0 means exponent one,
so no zero-modulus exception is required; both projections are covered by hf;
over the empty scheme both sides are the unique morphism. The detection proof
uses the universal limit cone and does not assume surjectivity of projections.

## New nodes

`lem-sfb-diagonal-trace-finite-integral-projection`, in the item's chapter and unit,
states the finite normalized projection equation in its own new module. Its
proof plan identifies the positive Cartier reduction and canonical source,
transports the constructed trace through the specified comparison squares, and
applies the existing finite projective-line integral identity. The blueprint
search found `det-sp-p1-trace` and `lem-sp-p1-diagonal-integrals-family`; these
assert the finite geometric identities, not the comparison equation for a given
completed diagonal and given normalized Result. No duplicate is introduced.
No change record is needed: no existing interface changes.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
