## What changed

Reduce `WeilConjectures.PurityFiniteSetting.chartGamma_eq_inverseOrientation`
without changing its statement or any existing definition. Its proof identifies
`chartProjectionUnitSource` with the actual reassociation, tensor-unit and unitor
composite, using the two existing unique-existence witnesses. It then applies the
proved coefficient-unit projection calculation.

That calculation is in the new module
`Sheaf.Paper.ProjectionUnitPresentationNormalization`. It specializes the existing
`projection_presentation_coordinate`, expands the smooth tensor map, uses the
separate tensor-mate unit identity, and cancels the unit constraints by naturality.
Its private categorical helper is proved. The separate module keeps this calculation
out of the large chart file after profiling and removing an unnecessary local
base-structure construction. No time limit or transparency check is disabled.

The new module `Sheaf.Paper.SmoothPurityTensorUnit` isolates the remaining unit
coherence calculation, without orientations, dimensions, affine towers or Tate
shifts. Its unit map is the existing actual composite, with no arbitrary choice
or duplicate definition. Proof imports stay private; all existing public imports,
signatures, definitions, attributes and the unit route are retained.

Validation: `lcompile.py --all` compiled all three sandbox modules in import order,
with diagnostics removed and the per-file limit enforced.

## Proved and sorry left

One of the original six holes is closed:
`WeilConjectures.PurityFiniteSetting.chartGamma_eq_inverseOrientation`.
The new theorem
`WeilConjectures.PurityFiniteSetting.projection_unit_presentation_normalization`
is proved and adds no hole.

One new hole is added:
`WeilConjectures.PurityFiniteSetting.smoothPurityTheta_unit`
(node `lem-pur-smooth-tensor-mate-unit`). This is a decomposition, with zero net
change in the packet's hole count, not a proof of the entire normalization theorem.

The five untouched original holes, all attached to
`lem-pur-diagonal-dnc-chart-normalization`, are:

- `WeilConjectures.PurityFiniteSetting.diagonal_dnc_chart_normalization`;
- `WeilConjectures.PurityFiniteSetting.chartOrientation_etale_restriction`;
- `WeilConjectures.PurityFiniteSetting.chartOrientation_open_baseChange`;
- `WeilConjectures.PurityFiniteSetting.chartEpsilon_standing_composition`;
- `WeilConjectures.PurityFiniteSetting.chartDiagonalDelta_coordinate_identity`.

Thus the item has five holes, the unit-coherence module has one, and the new
projection-normalization module has none. Existing integration obligations used
by the already proved `projection_presentation_coordinate` remain in their own
modules and are not restated here.

## No longer needed

None. No existing imports, declarations, modules or dependency nodes are removed.
Dependencies of the five untouched obligations and the source/unit route remain.
The Gamma proof uses existing projection agreement and its canonical coordinates;
it needs no new affine-tower induction or integration construction.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The DAG describes specialization of projection
agreement at the unit, but the library lacked the resulting identity for
`smoothPurityTheta` in the precise comparison coordinates. The new unit node
isolates that coherence step. The ordinary tensor-unit calculation is already
proved privately in `DualizingUnitComposite` from
`projectionMap_rightUnitality`; its pro-etale comparison coordinates still require
identification. Existing chart-mate modules depend on this item, so importing them
back into it would create an import cycle.

## New nodes

`lem-pur-smooth-tensor-mate-unit`, realized by
`Sheaf.Paper.SmoothPurityTensorUnit`, is the single remaining obligation. Its proof
in words uses ordinary projection-unit/counit normalization, tensor-unit site
comparison and cancellation of the comparison adjunction unit. It has no affine
projection, orientation, dimension or normalization assertion and is strictly a
part of the chart argument.

`lem-pur-projection-unit-presentation-normalization`, realized by
`Sheaf.Paper.ProjectionUnitPresentationNormalization`, is proved from the existing
presentation-coordinate theorem and the unit-coherence statement. It contains the
actual tensor/unitor naturality and cancellation argument. The item additionally
identifies its chosen chart source with these coordinates, so neither the new
hole nor the combining argument merely renames the original theorem.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
