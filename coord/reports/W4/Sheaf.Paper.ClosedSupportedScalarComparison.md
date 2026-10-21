## What changed

Proved `SheafOfModules.ScalarPullback.closed_supported_scalar_comparison` in
`Sheaf.Paper.ClosedSupportedScalarComparison`, following the node's four-step argument.
A proved private helper expands `closedScalarMap` componentwise using the whiskered
adjunction. The scalar adjunction makes `mU.T` preserve zero objects; the specified
open comparison transports the old closed-support assertion to the new coefficients.
The supported closed unit, inverse theta and scalar image of the old closed counit
are all invertible. The adjunction Hom equivalence proves the exact normalization,
and its injectivity proves uniqueness. Existing signatures, definitions and imports
are unchanged.

## Proved and sorry left

Closed 1 hole:
`SheafOfModules.ScalarPullback.closed_supported_scalar_comparison`
(node `lem-sfb-closed-supported-scalar-comparison`).
Added 0 holes. No sorry remains in the item module; no split-off statements.
The proof uses the supplied calculus and scalar-comparison hypotheses, as intended
by the node. It does not claim that their underlying construction theorems are closed.

## No longer needed

None. No import, dependency node or module is pruned. The proof follows the existing
DAG route, including the scalar adjunction's zero-object argument. No extra proof
imports were needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The proof works with the supplied unbounded
adjunctions and comparisons, without flatness or boundedness. The zero-source
argument also covers zero objects and empty open or closed pieces. No public
interface or target statement changed; no consumer adaptation or change record
is necessary.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
