## What changed

Closed the `finiteCompactSupportEvaluationRefinement` hole by reducing the evaluated
composition exchange to the existing finite relative compact-support evaluation theorem.
The ordinary proper exchange, ordinary compact-support exchange, and evaluation map now
use the canonical constructions from `RelativeCompactSupportPasting`. Added the public relative compact-support import and proof
import `Sheaf.Paper.CompositionExchangeTowerH` and its isolated compatibility statement.

## Proved and sorry left

Closed: `finiteCompactSupportEvaluationRefinement` (1 hole).

Remaining in `Sheaf.Paper.FiniteCompactSupportEvaluationRefinement`: `refinement_evaluation`,
`ordinaryC_identity_composition`, `ordinaryC_exchange`, and `ordinaryE_specified` (4 holes).
Added: `AlgebraicGeometry.ProEtale.StrictTower.compositionE_eq_towerH` (1 split-off hole).

## No longer needed

None. No existing DAG node or import was pruned.

## Where the brief, the DAG or earlier work was wrong

The target's existing composition exchange and the relative compact-support finite
evaluation theorem use the same mate and beta factors but with different associator
presentations. The required compatibility was absent as a named dependency, so it is
recorded as the strict constituent split-off node `new-finite-compact-support-composition-tower-exchange`; see `coord/changes/finite-compact-support-evaluation-refinement.md`.

## New nodes

`new-finite-compact-support-composition-tower-exchange` records the equality between
`compositionE` and the associator-expanded `RelativeCompactSupport.towerH`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
