## What changed

Completed `AlgebraicGeometry.FineFan.sharp_section_basic_chart_data` in
`lean/Sheaf/AlgebraicGeometry/SharpSectionBasicChartData.lean`, preserving its signature.
Proved private helpers implement local equality of germs, section separation, sharpness
of sections, openness of the unit-germ locus, basic-open intersections, localization
fraction formulas and uniqueness, sharpening descent, and restriction compatibility.
All data are constructed from fractions, colimit maps, and quotient maps; no new
unproved statement supplies data.

Updated the item's node proof step 6 and its proof dependencies to record the direct
cross-multiplication argument for restriction compatibility. No other existing module
or node is changed. The public import pruning is documented in
`coord/changes/G7-sharp-section-chart-import-pruning.md`.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.FineFan.sharp_section_basic_chart_data`
(node `lem-trf-sharp-section-basic-chart-data`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivery: 0.
No split-off statements or new axioms. The complete proof compiled in 8.8 seconds.
An explicit `#print axioms` check returned exactly `propext`, `Classical.choice`,
and `Quot.sound`; its temporary diagnostic command was removed. The final delivery
checks also compile the version with the unused-variable warning resolved.

## No longer needed

The proof does not use `AlgebraicGeometry.FineFan.affineFan_localization_sections`
(node `lem-trf-affine-fan-localization-sections`, module
`Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`). The formal statement
already expresses compatibility by equality of ambient fractions. Cross multiplication
and the restriction of both denominators to 1 prove this directly. Its statement
reference is preserved in `stmt_deps`; it is removed from `proof_deps` and the proof
step's uses. Removed the corresponding public import. There are no current direct Lean importers of the item, so no consumer adaptation is needed.
No further planned proof dependency is unused. No module is withdrawn, and no unit
statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared affine-section dependency is unnecessary for the ambient-fraction
formulation of the conclusion. No mathematical statement is disputed or changed.
The ILO VIII 3.1.1--3.1.8 source (printed pp.98--99) was read locally; the proof
supplies the details called straightforward there. Edge cases include the empty
space and empty open (section separation), the empty prime, the identity denominator,
and noncancellative target monoids (only cancellation in the source completion is used).
The three search modes were run; no existing theorem gave this monoid-sheaf result.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
