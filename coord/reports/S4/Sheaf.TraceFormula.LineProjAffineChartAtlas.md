## What changed

Repaired the return on delivery `0d6273ff9f6`: removed the duplicate private proofs of
`lineProj_mem_generator_open` and `lineProj_open_generator` from
`LineProjFractionCoefficientHom`. The original proved versions in `LineProjGenerationLocus`
are now public, documented and recorded in that node's Lean attachment. The coefficient
module imports that module privately and uses those theorems. The dependency graph records
this shared proof dependency; there is no import cycle.

Proved `AlgebraicGeometry.Scheme.Modules.exists_lineProj_affine_chart_atlas` with its
original statement. The proof constructs the unique homogeneous fraction charts, identifies
their positive-degree generation locus, proves arbitrary-degree and arbitrary-base overlap
compatibility, and supplies both source and base refinements and every local-frame formula.

Moved all thirteen unchanged chart definitions into
`Sheaf.TraceFormula.LineProjFractionChartData`, publicly re-exported by the item. Added fully
proved modules `LineProjFractionCoefficientHom`, `LineProjGenerationLocus`, and
`LineProjFractionCompatibility`. The generation argument uses the canonical tensor-pullback
stalk comparison and the ideal of nonunits of a local ring. Same-base overlaps use Mathlib's
`Proj.fromOfGlobalSections` after a local frame; affine-base transitions follow directly from
fraction uniqueness and `Proj.awayι_comp_map`.

All five delivered Lean modules compile. The sole existing direct consumer,
`Sheaf.TraceFormula.LineProjChartPullback` (held by T1), also compiles byte-for-byte unchanged.
The source-library boundary is respected: no file under `lean/WeilConjectures` is changed.
The extraction is documented in
`coord/changes/line-proj-fraction-chart-data-extraction.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_lineProj_affine_chart_atlas`
(node `lem-trf-line-proj-affine-chart-atlas`).

Added zero holes. There are zero `sorry` occurrences in the five delivered Lean modules.
The three new component results and all their helpers are completely proved. In particular,
`exists_lineProj_fraction_coefficient_hom`, `lineProj_exists_chart`,
`lineProj_trivialization_formula`, `lineProj_generator_stalk`, `lineProj_generation_locus`,
and `lineProj_fraction_compatibility` are proved. This is one hole closed, not a decomposition
into postponed statements. Existing dependency declarations may still depend on their own
upstream holes, as permitted by the stage brief.

## No longer needed

The two duplicate private generator proofs in `LineProjFractionCoefficientHom` are removed;
the single proved copies in `LineProjGenerationLocus` supply every use.

Removed the item's proof imports of
`WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`,
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`, and
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`. The adjunction remains used privately by the
coefficient module; it is not pruned from the argument. Removed the unused public import of
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` in the extracted data module;
no denominator-clearing result is used.

The atlas proof no longer needs
`lem-weil-pbc-nonvanishing-section-trivializes`: its local basis/germ characterization is
proved directly from the existing free-generator and invertible-module APIs.
It no longer needs `lem-weil-pbc-module-pullback-affine-sections`: the generation-locus proof
uses `lem-weil-pbc-module-stalk-pullback`, and base restriction compares maps into the original
chart on original fractions, so no affine tensor-section presentation is required.
It no longer needs `lem-weil-pbc-proj-basic-open-intersection`: on a common local frame both
maps equal the same ordinary Proj morphism, regardless of the denominator degrees.
These are dependencies pruned from this argument, not withdrawn source declarations.
No existing Lean module is withdrawn, and no global claim of unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated two private generator lemmas across its new modules; this
repair consolidates them as requested. No statement error. The explicit different-degree denominator calculation and the affine
base-change numerator expansion in the original plan were unnecessary. The local-frame
Proj API and fraction uniqueness give shorter complete proofs. The stalk argument for the
surjectivity union requires neither quasi-coherence nor finite generation beyond the stated
input. The unit route through graded line-module relative Proj is unchanged.

## New nodes

`lem-trf-line-proj-fraction-coefficient-hom` owns the proved coefficient ring map, unique
charts, source-restriction API, and frame formulas. It uses ordinary localization locally
and unique basis coefficients plus the sheaf condition globally, including zero divisors
and exponent zero.

`lem-trf-line-proj-generation-locus` owns the proved generator-germ equivalence and the
positive-degree surjectivity union. It uses the existing canonical tensor-pullback stalk
comparison; the generic off-unit use is declared in its split report.

`lem-trf-line-proj-fraction-compatibility` owns the proved arbitrary-base overlap and affine
refinement theorem. It compares local-frame charts with `Proj.fromOfGlobalSections`, then
uses homogeneous-localization naturality and local equality of scheme morphisms.

Updated the item's proof route and the existing
`def-trf-line-proj-fraction-chart-data` Lean attachment to the extracted module. Three kinds
of Mathlib search are recorded for each new statement. All new nodes are proved in this
session; none is split off for another worker.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
