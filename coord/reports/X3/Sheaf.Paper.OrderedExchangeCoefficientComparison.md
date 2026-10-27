## What changed

In `Sheaf.Paper.OrderedExchangeCoefficientComparison`, proved the existing
`lambda_existsUnique` statement with its original complex normalization. No public
statement, definition body, public import, or target changed.

Use the existing ordinary limit comparison and preservation of K-injective towers by
scalar restriction. Compare the two right-derived universal units, descend the
comparison, and cancel the exact-restriction factor maps to obtain the equation on
every complex. K-injective resolutions give uniqueness.

The three new helpers are private and fully proved. Proof-only imports of
`StrictTowerExchangeMateNormalization` and `FlatScalarTowerLimitSquare` expose their
existing K-injective preservation and derived comparison helpers. The existing DAG
node records the formalized derived-limit argument.

Validation: the final item module compiled through `lcompile.py` in 25.1 seconds
(`compile35.log`), with six original holes retained and no new holes.

## Proved and sorry left

Closed 1 of the original 7 holes:

- `AlgebraicGeometry.Scheme.OrderedExchange.lambda_existsUnique`.

Added 0 holes; split off 0 statements. Six existing holes remain unchanged:

- `AlgebraicGeometry.Scheme.OrderedExchange.ordinaryRho_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.rho_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.restriction_complete`.
- `AlgebraicGeometry.Scheme.OrderedExchange.phi_existsUnique`.
- `AlgebraicGeometry.Scheme.OrderedExchange.rho_unit`.
- `AlgebraicGeometry.Scheme.OrderedExchange.coefficientComparison`.

All seven belong to node
`lem-weil-pbc-ordered-exchange-coefficient-comparison`. The proof uses the existing
K-injective derived comparison API; this report does not claim all imported
mathematical dependencies are sorry-free.

## No longer needed

None. No original imports, nodes, modules, declarations, or unit steps are withdrawn.
The remaining planned dependencies are still needed by the six retained obligations.
No new intermediate statement is left for another worker.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The declared small-site balancing and completion
interfaces require transport before application to this module's original-site
presentations. The derived-limit proof uses the existing generic K-injective comparison
helper with the same mathematical argument.

An attempted rho proof from ordinary balancing and flat-term K-flat resolutions was
not retained: its concrete counit specialization repeatedly exceeded the file compile
limit. Profiling identified expensive definitional comparisons of the reduction
counits and complex-unit constructions. The delivered packet contains only the
verified lambda argument, and restores the original rho hole and its dependencies.

The launcher refreshed `.budget` during the resume: the original start was
1792758691, and the resumed metadata start is 1792773450.59202. The sandbox and item
remained `X3/Sheaf.Paper.OrderedExchangeCoefficientComparison`; the worker did not
edit this metadata. No delivery had been started before the resume.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
