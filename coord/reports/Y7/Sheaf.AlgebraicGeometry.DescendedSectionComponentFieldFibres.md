## What changed

Proved `AlgebraicGeometry.descended_section_component_field_fibres` along the existing
four-step DAG route. The canonical cartesian fibre comparison supplies the isomorphism,
and a pullback lift supplies the residue-field section. A proved private topological
helper identifies the inverse image of a relative component under an embedding with
its corresponding component. The connected open then admits the restricted rational
section, so the existing rational-point criterion proves geometric connectedness.
Finally, connectedness of a geometrically connected fibre makes this component the
whole fibre, and surjectivity of the field-extension projection descends that equality.

The theorem's signature, hypotheses, and conclusion are unchanged. Replaced the broad
public imports of `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and
`Mathlib.AlgebraicGeometry.Geometrically.Integral` with `Mathlib.AlgebraicGeometry.Fiber`.
No shared definition or other module is changed. The downstream tool reports zero
importers. The import change is recorded in
`coord/changes/descended-section-component-field-fibres-imports.md`.

## Proved and sorry left

Closed the sole hole, in `AlgebraicGeometry.descended_section_component_field_fibres`
(node `lem-trf-descended-section-component-field-fibres`). Added zero holes and zero
split-off statements. No `sorry` remains in the item module. The final module compiled
cleanly through `lcompile.py` in 3.8 seconds, with no warnings.

## No longer needed

Removed the unused public imports `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
and `Mathlib.AlgebraicGeometry.Geometrically.Integral`; the fibre constructions needed
by the statement come directly from `Mathlib.AlgebraicGeometry.Fiber`. The Picard/module
base-change conventions and geometric-integrality infrastructure of those imports are
not used by this proof. This does not withdraw their declarations or modules.

None of the declared proof dependencies is pruned: all four steps of the existing
DAG proof are used. No new proof imports are required; the rational-point criterion
is already available from the module's existing private import.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The statement already has all the data needed
for the direct proof, and the existing source-library rational-point criterion is proved.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
