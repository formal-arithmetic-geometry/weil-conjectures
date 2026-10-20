## What changed

Retired `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`, as assigned by
`coord/retire-items.tsv`, through `deleted.txt`. The node
`lem-sbc-quasi-finite-polynomial-chart` now records the existing declaration
`AlgebraicGeometry.exists_quasiFinite_polynomial_chart` in
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart`, with its actual
signature. The node's mathematical statement, proof steps and dependencies stay
unchanged. The upstream module and every target declaration are untouched.

The sole remaining direct importer,
`Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension`, drops its unused import
of the withdrawn module, without a replacement import. This repairs point 5 of
reviewer C-c0899's return of delivery c08996ce41. The import removal is its only
change; its three signatures, docstrings and theorem bodies are unchanged. The
adapted consumer compiles without warnings using `lcompile.py` (exit code 0).
A scratch check also compiles both conversions between
the old and retained conclusion packagings. `#print axioms` on the retained
`AlgebraicGeometry.exists_quasiFinite_polynomial_chart` reports precisely
`propext`, `Classical.choice` and `Quot.sound`.

Change record: `coord/changes/S3-retire-quasi-finite-polynomial-chart.md`.

## Proved and sorry left

This is a retirement of a duplicate whose assigned module already has zero
holes: proved 0 of 0, added 0, split off 0. The retained upstream theorem has a
complete proof from `exists_fiber_dimension_nat` and
`exists_quasiFinite_polynomial_chart_data`. No theorem proof is replaced by a
hole, and no new declaration is introduced.

Three existing holes in the adapted consumer remain untouched, all belonging to
node `lem-pur-cohen-macaulay-field-extension`:

- `AlgebraicGeometry.stalk_depth_eq_ringKrullDim_iff_of_field_extension`.
- `AlgebraicGeometry.fibre_depth_eq_ringKrullDim_iff_geometric`.
- `AlgebraicGeometry.fibre_depth_eq_ringKrullDim_locus_baseChange`.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`. Its only
remaining importer drops the unused import without replacement. In particular,
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart` is not added as an
import of `Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension`. The duplicate's
five public imports and two proof imports disappear with that duplicate; the
upstream implementation retains its existing public imports and proof imports.
The retired module's removed imports, all still needed by the canonical module,
are:

- `Mathlib.AlgebraicGeometry.AffineSpace`.
- `Mathlib.AlgebraicGeometry.Fiber`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`.
- `WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Dimension`.
- `WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`.

No mathematical node or dependency is pruned. In particular,
`lem-sbc-quasi-finite-polynomial-chart-dimension` and
`lem-sbc-quasi-finite-polynomial-chart-chart` remain needed by the upstream proof
and already attach to upstream modules. Parents still cite the same chart node,
now realized by the upstream theorem, so no parent proof or unit step is
bypassed. The formerly listed Sheaf consumers
`Sheaf.AlgebraicGeometry.AffineBaseFlatQuasiFiniteChartCore` and
`Sheaf.AlgebraicGeometry.AffineFibreCohenMacaulayLocus` are already absent from the
current source; their upstream counterparts import the canonical module already.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a deep outstanding obligation, whereas the
current queue explicitly assigns this item as `retire`. The current assigned
module has no `sorry`. The retirement table's three consumers have reduced to
one in the current source; a whole-library import search and `downstream.py`
confirm that only `Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension` remains.
There is no rework entry for this module. Reviewer C-c0899 returned delivery
c08996ce41 because replacing the consumer's unused import was unnecessary; this
repair removes that import instead.

The retained theorem packages affineness and membership using conjunctions;
the duplicate instead quantified proofs existentially. Both statements give
exactly the same open, affineness proof, membership proof, dimension, morphism
and properties. Their hypotheses, universes and mathematical conclusion agree.
Only the Lean attachment and the removal of the unused consumer import change.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
