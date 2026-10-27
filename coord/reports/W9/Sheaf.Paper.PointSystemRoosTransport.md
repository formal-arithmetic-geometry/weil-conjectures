## What changed

Closed `WeilConjectures.PointSystemRoos.exact_products` by applying the stronger
`PointSystemNormalizedComparison.exact_products` theorem already assigned as a proof
dependency. Added proof-only imports of `Sheaf.Paper.PointSystemNormalizedComparisonData`
and `Sheaf.Paper.PointRestrictionWholeRoosSquare`.

## Proved and sorry left

Proved: `exact_products` (one of two original holes).

Sorry left: `point_system_roos_transport`, the final whole-Roos assembly theorem
(blueprint: lem-trf-point-system-roos-transport). No new sorry was added.

## No longer needed

None. The imported normalized comparison and whole-Roos square modules are the stated
proof dependencies of the remaining theorem.

## Where the brief, the DAG or earlier work was wrong

The final theorem depends on two very large existential interfaces whose derived
comparison functors are packaged existentially, while `Data` requires a concrete
localized natural transformation with a specific interface. The exactness subclaim,
however, matches the normalized-comparison dependency directly and is independently
proved here.

## New nodes

None.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
