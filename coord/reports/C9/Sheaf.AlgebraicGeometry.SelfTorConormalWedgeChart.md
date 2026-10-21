## What changed

This is the authorized retirement of the duplicate Sheaf chart module. The file
`lean/Sheaf/AlgebraicGeometry/SelfTorConormalWedgeChart.lean` is withdrawn via
`deleted.txt`, and its DAG node is attached to the complete upstream twin
`WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChart`.

The direct consumer
`lean/Sheaf/AlgebraicGeometry/SelfTorBasicIdealWedgeCoordinates.lean` now imports
the upstream chart theorem and
`Sheaf.AlgebraicGeometry.ExteriorSheafComparison`. It composes the upstream
`exteriorPower` chart with `exteriorSheafIsoExteriorPower`, proves the transported
normalization using `exteriorSheafIsoExteriorPower_hom_wedge`, and keeps its
existing public statement and definitions unchanged. The consumer compiles
against the delivered overlay in 15 seconds. The delivery checks and axiom probe pass.

The node proof and proof dependencies were updated to record the upstream
attachment and the actual transport route. The retirement change record is
`coord/changes/retire-self-tor-conormal-wedge-chart-C9.md`.

## Proved and sorry left

The assigned item has zero current `sorry` holes: it is a retirement repair.
Holes closed: 0. Holes added: 0. No `sorry` remains in either delivered Lean proof. The upstream declaration
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart` is complete, and the
adapted consumer's declaration
`AlgebraicGeometry.exists_basic_ideal_wedge_selfTor_coordinates` remains
unchanged and complete.

## No longer needed

The duplicate module `Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart` is no
longer needed and is listed in `deleted.txt`. Its direct import and declaration
use are replaced by the upstream module and the canonical exterior comparison.
The former duplicate-only route through the Sheaf chart is pruned; the upstream
section-equivalence and target-localization dependencies remain needed by the
consumer's proof. No other reached module is removed.

## Where the brief, the DAG or earlier work was wrong

The retirement inventory correctly marked this pair `PROOFDIFF_UNSAFE`: the
upstream theorem uses `exteriorPower` and `wedge`, whereas the duplicate's
consumer-facing theorem uses `exteriorSheaf` and `exteriorSheafSection`. A plain
import substitution is therefore insufficient. The adaptation must explicitly
transport the chart through `exteriorSheafIsoExteriorPower` and use its pure-wedge
formula. The adapted proof makes this conversion and preserves the consumer's
statement exactly.


Self-checks: the upstream signature matches the mathematical node, the consumer
public signature and public imports are unchanged, and the canonical wedge
comparison includes degree zero, empty charts, and zero quotient rings. No new
node was introduced.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
