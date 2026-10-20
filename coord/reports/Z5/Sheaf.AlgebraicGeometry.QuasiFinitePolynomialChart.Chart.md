## What changed

Retire the duplicate module
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart` as assigned by
`coord/retire-items.tsv`. Its sole direct consumer,
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`, now privately imports
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`.
The consumer's theorem signature and complete proof stay verbatim: its existing
`obtain` pattern also unpacks the upstream conjunctions. Redirect
`lem-sbc-quasi-finite-polynomial-chart-chart` to the existing upstream theorem,
recording its verbatim signature. No source-library file changes.

Change record: `coord/changes/Z5-retire-quasi-finite-polynomial-chart-chart.md`.

## Proved and sorry left

This retirement repair starts with zero holes. Holes closed: zero; holes added:
zero; holes left: zero. Nothing is split off.
`AlgebraicGeometry.exists_quasiFinite_polynomial_chart_data` already has a complete
proof in the upstream twin, and
`AlgebraicGeometry.exists_quasiFinite_polynomial_chart` keeps its complete proof.
The old module and the original consumer both compiled cleanly before the change.
The adapted consumer compiled cleanly in 6.1 seconds against the upstream
theorem. The delivery's axiom probe found no disallowed axioms, and the
required `deliver3.py --no-push` dry run passed compilation and preflight
(review class CODEX). A whole-library
import scan finds one direct consumer and one further transitive importer,
`Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension`; only the direct consumer
mentions the replaced declaration. Compiling both modules together in import
order also succeeds: 2.4 seconds for the adapted parent and 3.1 seconds for its
unchanged transitive consumer. `tools/downstream.py --uses` independently
confirms this two-module closure and its single declaration user.

## No longer needed

Withdraw `lean/Sheaf/AlgebraicGeometry/QuasiFinitePolynomialChart/Chart.lean`
through `deleted.txt`, leaving no import of that module. Remove its sole consumer's
private import of `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`.
The retired copy's public imports of `Mathlib.AlgebraicGeometry.AffineSpace`,
`Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
`WeilConjectures.Mathlib.Topology.KrullDimension`, and its private imports of
`Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra`,
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension`
and `WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.LocalizedChart`
are consequently removed from that copy. The upstream twin imports its own proved
ring theorem and the same two geometric bridges. Those three mathematical
proof dependencies remain necessary; none of their nodes is pruned.
No claim is made that the ring theorem's Sheaf copy is globally unused.
The chart node remains attached to its upstream realization.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe this zero-hole retirement. The actual
assignment is the `retire` row in `coord/retire-items.tsv`, under the human's
2026-10-20 retirement instruction. The old DAG attachment points to a duplicate
Sheaf declaration although upstream already proves the same mathematical result.
The new attachment fixes that mismatch. The difference in existential packaging
adds no hypotheses, removes no cases (including fibre dimension zero), and weakens
no conclusion. The blueprint unit's route and the node's three proof steps stay.

Searches through `msearch.py`: LeanFinder returned affine-space presentation and
quasi-finiteness criteria; Loogle did not recognize `AffineSpace`; grep found the
Zariski Main Theorem and quasi-finite ring infrastructure. Local searches found
the exact already-proved upstream twin, which supplies the shortest route.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
