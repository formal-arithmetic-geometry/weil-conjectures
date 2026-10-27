## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralSectionScalars.scalarComparison` in
`Sheaf.Paper.IntegralSectionRegularScalarsScalar`, retaining its statement. Both
regular values are identified with the unit module. Naturality of the scalar-extension
adjunction handles the continuous scalar functor; the already proved
`completedKoszulOne` isomorphism and scalar formula handle completed constants.
The normalized positive-quotient projections identify the two coefficient maps.
Unit-module extensionality then gives the required scalar intertwining equation.
All auxiliary declarations are private and proved. The item's DAG proof and
proof dependencies record these concrete steps.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.IntegralSectionScalars.scalarComparison`
(node `lem-sfb-integral-section-regular-scalars-scalar`). No holes added or split off.
No `sorry` remains in the delivered module. The final single-file remote compile
passed without warnings in 42.6 seconds, below the 60-second limit.

## No longer needed

No original dependency node or module is pruned: the original seven dependencies
supply data or regular-module and normalized-projection APIs used by this proof.
No new finite-presentation argument, quotient-comparison lemma, or additional
completed-realization theory is required. Existing proved helpers suffice.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing plan closes using the already
proved normalized constant-section projection and completed regular scalar APIs.
The DAG now explicitly records those APIs and their point-comparison and
constant-generator normalization helpers. The zero scalar and empty scheme require
no nonzero, nonempty, boundedness, or finiteness hypotheses beyond the statement.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
