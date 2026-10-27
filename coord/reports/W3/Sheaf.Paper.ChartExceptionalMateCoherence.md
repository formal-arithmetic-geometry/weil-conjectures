## What changed

Replaced the main theorem's hole by a complete assembly of the counit equation,
three factor squares and epsilon pasting. Added proved private categorical lemmas
`transport_identity`, `transport_composition` and `reverse_square`, and a proved
`omega_bounded` lemma. The latter uses ordinary smooth exceptional constructibility
and the actual diagonal comparison, including constructibility of the constant sheaf.
The two etale-origin domain conditions are derived, not added as assumptions.
The counit equation alone implies invertibility of the specified composition map.

The five remaining obligations have separate modules and nodes with unchanged
coefficient range and explicit proofs in words. The main theorem keeps its exact
statement, definitions and public imports. Its node now records the actual route.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.ChartComparisons.chart_exceptional_mate_coherence`
(node `lem-pur-chart-exceptional-mate-coherence`), from the following strictly
smaller obligations. This is a decomposition, not a net proof gain.

Five holes added, one per new module:

- `chart_exceptional_counit_equation` (`lem-pur-chart-exceptional-counit-equation`).
- `chart_epsilon_pasting` (`lem-pur-chart-epsilon-pasting`).
- `chart_diagonal_source_square` (`lem-pur-chart-diagonal-source-square`).
- `chart_dnc_square` (`lem-pur-chart-dnc-square`).
- `chart_normal_integration_square` (`lem-pur-chart-normal-integration-square`).

All five declarations are in namespace
`WeilConjectures.PurityFiniteSetting.ChartComparisons`. No other sorry is added.
The original item has zero holes after the decomposition; original count: one.

## No longer needed

The main proof does not need the separate geometric proof of identity/composition
for q or r (old proof Step 9). These laws follow formally from the already required
alpha and delta squares and epsilon pasting. No geometry or unit route is bypassed.

Removed direct proof imports from the item:

- `Sheaf.Paper.ChartCartesianDomain`.
- `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange`.
- `Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame`.
- `Sheaf.Paper.DualizingSigmaCocycleLocality`.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`.
- `Sheaf.Paper.PuritySectionEtaleRestriction`.
- `Sheaf.Paper.SmoothExceptionalTensorPasting`.
- `Sheaf.Paper.VectorIntegrationSiteComparison`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`.

The geometric and integration nodes remain dependencies of the corresponding
new factor-square nodes; their modules are not globally withdrawn. No source-library
declaration or module is removed. The direct use of CompositionTensorMate was
investigated and discarded: the counit equation already supplies invertibility.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The old plan's separate q/r pasting calculations are
unnecessary once the factor squares are available. The diagonal-normalization
module contains tempting orientation theorems, but its node depends on this item;
using those would create a mathematical dependency cycle, so the proof avoids them.
The narrower `chart_dnc_vector_factors` theorem requires an unramified coefficient
hypothesis and cannot prove this item for arbitrary E. Only its existing construction
definitions are used here, as in the original statement.

## New nodes

`lem-pur-chart-exceptional-counit-equation` isolates only the equality of the specified
standing compositor followed by rho with epsilon; domain and invertibility are proved
in the item. `lem-pur-chart-epsilon-pasting` isolates only epsilon's identity and
composition. `lem-pur-chart-diagonal-source-square`, `lem-pur-chart-dnc-square`, and
`lem-pur-chart-normal-integration-square` isolate the three individual equations,
respectively. Each is strictly a part of the original theorem and has its own source,
complete proof in words and Lean module. No definition or existing statement changes,
so no change record is needed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
