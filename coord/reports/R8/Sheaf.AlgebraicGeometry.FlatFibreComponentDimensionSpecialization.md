## What changed

Retired `Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization`, the
DIFFERENT twin listed in `coord/retire-items.tsv`, using `deleted.txt`.
Reattached `lem-sbc-flat-fibre-component-dimension-specialization-open` and
`lem-sbc-flat-fibre-component-dimension-specialization` to the existing declarations
in `WeilConjectures.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization`.
The latter's proof metadata now records that the upstream signature omits `hx'`.
The mathematical statements, proof dependencies and unit route stay the same.

The upstream neighbourhood signature is identical. The upstream specialization
theorem implies the old signature by an ordinary application, ignoring `hx'`.
Both implications were compiled in a scratch module. The upstream module and the
unchanged parent `WeilConjectures.AlgebraicGeometry.FlatClosedFibreInterior` were
also compiled individually through `lcompile.py --all` in import order, each in
under three seconds, without warnings. The parent already imports the upstream
replacement and applies its specialization theorem twice. No source-library file
or consumer needs an edit.

Change record: `coord/changes/R8-flat-fibre-component-specialization-upstream.md`.

## Proved and sorry left

The assigned module initially had zero direct holes. Closed zero holes; added zero
holes; zero holes remain in the withdrawn module. No statement is split off.
The two retained upstream declarations are:

- `AlgebraicGeometry.exists_fibre_dimension_open_of_flat_restrict`
  (`lem-sbc-flat-fibre-component-dimension-specialization-open`).
- `AlgebraicGeometry.fibre_dimension_eq_of_specializes_component_restrict`
  (`lem-sbc-flat-fibre-component-dimension-specialization`).

Their `#print axioms` results contain exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no sorry axiom. They were already fully proved upstream; this
packet repairs stale duplicate ownership and records no new proof or net hole
reduction. The old statements follow from them without adding any assumptions.
Empty schemes, an empty base open and absent fibre component points are handled
by the unchanged hypotheses; there is no new construction or existence choice.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization`.
Its four public imports (`Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
`WeilConjectures.Mathlib.Topology.KrullDimension`) and proof import
`WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrata` disappear from this
empty module. All those modules remain available and are still needed by the
upstream proof. No other node, module, dependency edge or source declaration is
pruned.

Checked every DAG node's statement dependencies, proof dependencies and proof-step
uses. The only external parent is `lem-sbc-flat-closed-fibre-interior`, whose
upstream Lean consumer already uses the upstream replacement. No live or
quarantined Lean module imports the Sheaf copy. Both node attachments are migrated,
so unfinished DAG parents continue to reach the same proved mathematics.
`dag/units/sk-prop-normal-form.json` has empty realized lists; no unit step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The proof brief is stale after upstream adoption: this module contains no `sorry`,
and its complete proofs already exist upstream. The retirement inventory marks
it DIFFERENT only because upstream removed the unused `hx'` binder from the
specialization theorem. That signature is stronger and proves the old node
statement unchanged. The two node attachments still named the unused Sheaf copy;
this delivery corrects them instead of restarting or decomposing the proof chain.
There is no mathematical dispute, no new node, and no forced adaptation.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
