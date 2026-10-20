# AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections

## Reason

Retire the listed `Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections`
duplicate in favor of the complete adopted upstream twin. The current queue row is
an explicit `retire` assignment and the upstream module contains the same theorem,
with the same `exteriorPower` encoding used by the current dependency graph.

## Old

The withdrawn Sheaf module declared the complete theorem
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections` in
`lean/Sheaf/AlgebraicGeometry/SelfTorConormalWedgeChartFromSections.lean`, with
`E := Scheme.Modules.exteriorSheaf N n` in its public statement.

## New

The node now attaches to the unchanged complete declaration
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_from_sections` in
`WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections`, whose
statement uses `E := Scheme.Modules.exteriorPower N n`. The two constructions are
identified by the proved comparison used by the adapted chart consumer, so the
mathematical node and its parent route remain unchanged.

The direct consumer
`Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart` now privately imports the
upstream twin and applies the upstream theorem to the existing affine section
map. It composes the resulting over-site isomorphism with
`Sheaf.AlgebraicGeometry.ExteriorSheafComparison`'s canonical exterior-sheaf
comparison, preserving the consumer's public `exteriorSheaf` statement.
No upstream file, target statement, definition, or public signature changes.

## Users

The current source scan finds one direct consumer. The listed transitive users
remain unchanged and continue to reach this node through the chart theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Replace the private duplicate import by the upstream twin and transport the upstream `exteriorPower` isomorphism through the proved comparison; public signature unchanged. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Transitive consumer; no change. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive consumer; no change. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive consumer; no change. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive consumer; no change. |

## Status

landed 20261020T233128-L-897642 2026-10-20 (merge of deliver/E7/Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections)
