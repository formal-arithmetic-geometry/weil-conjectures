## What changed

`finiteUnits` is now proved by assembling two strictly smaller component statements:
`finiteOpenTensor_isIso` for the finite open tensor mate and `finiteRingUnit_isIso` for the
finite reduction of the completed ring unit. The item module compiles with these declarations
and keeps the original target statement and definitions unchanged. The parent DAG proof step and
its dependency list record both new component nodes.

## Proved and sorry left

Closed one original hole:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteUnits`.

Added two strictly smaller split-off holes:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteOpenTensor_isIso`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteRingUnit_isIso`.

The five original helper holes still present are:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.strictUnits`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.completionUnits`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.exchangeSubstitution`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.twoSubstitutions`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.strictFiniteCoherence`.

## No longer needed

None. No imports, modules, or previously declared DAG nodes became unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned direct proof of `finiteUnits` requires an equivalence instance for the reduction
functor that is not available in the current declarations, and typeclass inference does not
establish the reduced completed ring-unit isomorphism. I therefore isolated the two actual
subcalculations as separate strictly simpler statements. This changes no target statement,
definition, or existing public signature.

## New nodes

Added `lem-cbc-completed-support-finite-open-tensor-iso` and
`lem-cbc-completed-support-finite-ring-unit-iso` in `sec-smooth-purity`, both attached to the
item module because their statements use the module's local `finiteOpenTensor` and `ringUnit`
definitions. Their docstrings and DAG records give the finite mate and normalized quotient-unit
proof obligations in words.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
