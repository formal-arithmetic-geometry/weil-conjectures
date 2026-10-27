## What changed

Reduced `AlgebraicGeometry.AlgebraicSpace.exists_ampleSchemeTestLinePreparation`
to three strictly partial obligations, preserving its full signature and every field
of `AmpleSchemeTestLinePreparation`.

The main proof now forms the site objects from explicit scheme pullback charts, applies
normalized line descent, proves ordinary tensor-pullback invertibility using
`invertible_pullback_tensor`, and applies
`isAmple_on_affineOpens_tensorPullback_baseChange` literally on the chosen scheme
pullbacks. The proved private helper `qcSeparated_of_relativeAmple` extracts compactness
from absolute ampleness on each affine inverse image, applies Mathlib's affine-open
criterion for `QuasiCompact`, and applies the final separatedness clause of the canonical
Proj criterion. The scheme-to-presheaf bridge supplies the geometric predicates. The
proof constructs every field of the original bundle, including its cartesian scheme
square by reflection through `Over.forget`, and retains the prescribed etale comparison.

Moved the six existing normalized section equations, with identical signatures and
bodies, into `Sheaf.TraceFormula.AmpleSchemeTestLinePreparationDefs`; the item publicly
reimports them. This permits the split statements to use those equations without an
import cycle. No source-library module was changed. Extraction and import visibility
are recorded in `coord/changes/ample-test-section-equations-extraction.md`.

Validation: all five modules compiled on the project server; the main assembly took
31.0 seconds, the others 2.7--8.9 seconds. The final compile of the pruned imports
passed for all five modules with no errors or warnings. Repository searches found no other direct Lean
importer of the item and no other Lean user of its six extracted names, so no consumer
adaptation was necessary.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.AlgebraicSpace.exists_ampleSchemeTestLinePreparation` (node
`lem-trf-ample-scheme-test-line-preparation`) by a complete Lean assembly. The private
lemma `qcSeparated_of_relativeAmple` and the three explicit chart-construction
definitions have complete proofs/bodies.

This is a decomposition of one original hole into three holes, not a proof free of
remaining dependencies. The item now has zero direct `sorry`s. The delivery adds exactly:

- `AlgebraicGeometry.AlgebraicSpace.exists_ampleSchemeTestCharts`, node
  `lem-trf-ample-scheme-test-charts`: geometry only, with no module or ampleness data.
- `AlgebraicGeometry.AlgebraicSpace.exists_ampleTestNormalizedLineData`, node
  `lem-trf-ample-test-normalized-line-descent`: normalized restriction/pullback/descent
  data only, with no base-scheme ampleness or quasi-compactness/separatedness conclusion.
- `AlgebraicGeometry.AlgebraicSpace.qcSeparatedPresheafMap_of_schemeCharts`, node
  `lem-trf-scheme-chart-qc-separated-presheaf`: recognition of presheaf predicates from
  already quasi-compact separated scheme charts; no line-module construction.

Each new hole is a public named theorem with whole body `:= by sorry`, its precise
source and full proof in words in the docstring, and a matching DAG node. The extracted
definition module has zero holes. All new data definitions are explicit constructions;
no arbitrary object is chosen from an unproved existence theorem in a definition.
Existing imported declarations with holes remain their own items.

## No longer needed

The following direct imports were removed from the item:

- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSections`
- `Sheaf.TraceFormula.SpaceQCSeparatedPointCover`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
- `Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison`
- `Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons`
- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`

These are direct-import removals, not whole-library module withdrawals. The normalized
comparison/descent imports remain needed in `AmpleTestNormalizedLineDescent`; the fibre
product/cover import remains needed in `AmpleSchemeTestCharts`; the point-cover locality
and closed-immersion base-change imports remain needed in
`SchemeChartQCSeparatedPresheaf`. Statement infrastructure is supplied by the extracted
definition owner and the remaining public imports. Mathlib scheme compactness facts
are available through the canonical-Proj criterion.

The original direct DAG proof edges to
`lem-trf-space-fibre-products-etale-covers`, `def-trf-algebraic-space`,
`lem-trf-scheme-etale-invertible-comparison`,
`lem-trf-etale-line-sections-normalized-comparisons`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`def-trf-space-module-scheme-restriction`, `def-pc-module-pullback`,
`lem-trf-algebraic-space-invertible-descent`,
`lem-trf-space-qc-separated-etale-local`, `lem-pc-quasi-compact-base-change`,
`def-weil-proper-morphism`, `lem-weil-pbc-closed-immersion-base-change`, and
`lem-sc-etale-qcoherent-presheaf-functorial` are replaced by edges to the appropriate
split steps. These mathematical dependencies remain needed below those steps or as
statement dependencies; none is claimed globally pruned. No module is withdrawn, and
no blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The eight-step plan combines several interfaces whose missing glue is substantial:
normalized ordinary identifications of `schemeRestriction`, coherent pullback of
transitions, uniqueness preserving all chart identifications, and scheme/presheaf
property recognition. The existing invertible-descent theorem also fixes its index
universe to the base universe and phrases joint surjectivity on scheme tests; the item
allows an arbitrary index universe and uses field-extension point surjectivity. The
normalized-descent proof text records the needed small-cover reduction explicitly.
These are gaps in the planned Lean assembly, not objections to using declarations
whose proofs still contain holes.

The relative-ampleness base-change theorem uses the actual categorical scheme
pullback, not an arbitrary isomorphic scheme chart. The geometric split therefore
chooses that exact scheme pullback and proves the original over-category cartesian
square in the final assembly. This avoids adding an unnecessary ampleness-transport
obligation.

The stronger generic normalized-line statement was checked for arbitrary/nonflat k,
empty covers and targets, repeated/self-overlap charts and large index universes.
It uses actual tensor pullbacks, preserves diagonal and triple cocycle conditions and
only defines etale restriction when k is etale. The geometric split imposes no module
hypothesis. The bridge imposes scheme quasi-compactness and separation separately and
keeps point-cover surjectivity; it does not replace it by objectwise section lifting.
The original parent ample-local route still needs the item, so nothing was withdrawn.

## New nodes

`def-trf-ample-test-normalized-section-equations` owns the six existing equations
extracted into `AmpleSchemeTestLinePreparationDefs`; their data and types are unchanged.
This is the only definition extraction.

`lem-trf-ample-scheme-test-charts` records Step 1 and the etale-projection part of Step 8
with explicit categorical scheme pullback charts. Its module also defines the concrete
over-scheme pullback and both projections, plus the geometric data structure.

`lem-trf-ample-test-normalized-line-descent` records Steps 3--5 and the final normalized
etale comparison in Step 8, independently of all relative-ampleness hypotheses.

`lem-trf-scheme-chart-qc-separated-presheaf` records Step 7's conversion from scheme
properties and the specified source cartesian squares to the existing presheaf
predicates, independently of line descent and ampleness.

The item node's `proof`, `proof_deps` and `proof_origin` now follow the complete Lean
assembly; its `lean.declarations` lists the structure and theorem that remain in its
module. Change record: `coord/changes/ample-test-section-equations-extraction.md`.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
