## What changed

Proved all three clauses of `AlgebraicGeometry.projectiveSpace_functor_of_points` without
changing its signature. The universal pair pulls back to an invertible module with
nonvanishing coordinates. Existence uses the already proved source
`ProjectiveSpace.exists_hom_twistRestrict` on the generating-locus cover. Uniqueness is the
proved private helper `projective_pair_injective`: the same generating loci give the same
chart preimages, free generators cancel the coordinate ratios, chart extensionality gives
local equality, and the cover gives global equality. Naturality follows from the existing
composition isomorphism and the naturality of the adjunction unit.

Two other proved private helpers compare tensor pullback with ordinary pullback and
express naturality on sections. Every new helper is proved. All new imports are proof-only.
The existing public imports and the public theorem statement are unchanged.

The DAG proof now records this source-library route. Two new nodes record already proved
source tools; they introduce no Lean module or obligation. The unit `sk-thm-reduction` and
its realized steps are preserved: this item realizes none of those steps directly.

Validation: the final module compiles without warnings in 21.9 seconds. A separate compiled
import of this exact sandbox module reports that `projectiveSpace_functor_of_points` uses
only `propext`, `Classical.choice`, and `Quot.sound`. The proof handles empty schemes and
`n = 0`; it requires no nonemptiness of the scheme or choices of arbitrary geometric data.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.projectiveSpace_functor_of_points`
(node `lem-weil-pbc-projective-space-functor-of-points`).

Holes added: zero. Split off: zero. Sorries left in the delivered Lean: none.
The three private helpers `tensorComparison_section`, `tensorPullback_section_naturality`,
and `projective_pair_injective` are proved, not new obligations. The new nodes attach to
existing source theorems, not to new declarations.

## No longer needed

Removed these seven proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf`.
- `Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`.
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor` (retired compatibility import).
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`.
- `Sheaf.Paper.NonvanishingSectionTrivializes` (retired compatibility import).
- `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback` (redundant proof import).

Removed the obsolete parent `tool_uses` approval for `lem-pur-sheaf-hom-is-sheaf`;
its remaining source-construction use is recorded on that source-tool node.

The parent proof no longer needs the following old proof-dependency edges:
`lem-weil-pbc-projective-space-twisting-sheaf-charts`,
`lem-weil-pbc-nonvanishing-section-trivializes`,
`lem-weil-pbc-invertible-generating-sections-fibre`,
`lem-weil-pbc-morphism-into-affine-scheme`, `lem-pur-sheaf-hom-is-sheaf`,
`lem-weil-pbc-invertible-pullback-invertible`, `def-pc-module-pullback`, and
`def-pc-representable-functor`.
The construction and affine correspondence are implemented by the already proved source
tools; the new source-tool nodes retain their mathematical dependencies where relevant.
The fibrewise-generation criterion is unnecessary because the theorem already assumes
pointwise nonvanishing. The universe-zero twisting-chart conjunction is replaced by the
proved universe-polymorphic coordinate-locus result. Invertibility is supplied by the
same tensor-pullback theorem already needed for composition. Pullback and representability
definitions remain statement/interpretation dependencies, not proof obligations.
No claim is made that other targets cease to need any of these modules.

## Where the brief, the DAG or earlier work was wrong

The planned local construction and gluing are already fully implemented in source
`ProjectiveSpace.OfInvertible`; reimplementing them is unnecessary. Source
`ProjectiveSpace.LinearCombination` supplies chart extensionality and the generation-locus
calculation needed for uniqueness. The recorded twisting-sheaf chart theorem is only at
universe zero with coordinate type `Fin (n+1)`, whereas this item uses arbitrary universe
`u` and `ULift (Fin (n+1))`; the independent proved standard-chart nonvanishing theorem has
the required generality. No existing statement or definition was changed.

## New nodes

`lem-weil-pbc-projective-space-free-frame-construction` records the existing source
`AlgebraicGeometry.ProjectiveSpace.exists_hom_twistRestrict`. This is the existence part
of Stacks 01N8 for a specified cover with free frames, with its actual ordinary-pullback
section formula. It has no sorry and introduces no module.

`lem-weil-pbc-projective-space-chart-ratio-extensionality` records the existing source
`AlgebraicGeometry.ProjectiveSpace.hom_ext_of_preimage_standardOpen_eq_top`. It is the
single-chart affine extensionality tool, requiring an affine base, equality over the base,
and equality of all coordinate ratios. It has no sorry and introduces no module.

The two existing source results are generic tools within the existing unit route.
No change record is needed: no public signature, definition, or visible import changed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
