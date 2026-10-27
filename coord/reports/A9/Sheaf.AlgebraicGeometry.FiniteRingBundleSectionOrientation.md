## What changed

Proved `finiteRingBundleSectionOrientation` and
`finiteRingBundleSectionOrientation_valuation` from the canonical integration mate,
affine normalization, and equality detection on affine frames. The original four
public theorem statements are unchanged.

Extracted the eighteen existing definitions and instances, verbatim and in order,
into `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData`; the original
module publicly re-exports it. This makes the canonical data available to the new
proof modules without an import cycle. No object is defined by arbitrary choice
from an existence statement. The inverse projection isomorphism is uniquely
specified by its inverse being the canonical projection arrow.

The new proved unit-isomorphism lemma uses finite-coefficient projection formula
and `vectorIntegrationMate_isIso`. The equality lemma identifies the source with a
shifted single flat Tate sheaf, transports concentration to the target using that
unit isomorphism, cancels open base change on affine frames, and uses faithful
restriction of degree -2d cohomology maps. Thus no derived morphism descent
existence theorem is needed for these two orientation proofs.

The data extraction and public re-export are recorded in
`coord/changes/A9-bundle-section-orientation-data.md`. Downstream consumers retain
the same definitions; in particular `Sheaf.Paper.FiniteRingSectionDeformation`
uses the same unit-map and unit-isomorphism constants. No consumer or source-tree
module was edited. No target statement or definition body changed.

## Proved and sorry left

Original holes closed (two of four):
- `AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation`.
- `AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation_valuation`.

New fully proved declarations:
- `AlgebraicGeometry.Etale.bundleSectionPurityUnit_exists_isIso`
  (`lem-trf-bundle-section-purity-unit-isIso`).
- `AlgebraicGeometry.Etale.bundleSectionOrientation_map_ext`
  (`lem-trf-bundle-section-orientation-map-ext`).

Original holes unchanged:
- `AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation_naturality`
  (`lem-trf-finite-ring-bundle-section-orientation`).
- `AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation_rankZero`
  (same node).

One new hole split off:
- `AlgebraicGeometry.Etale.bundleSectionPurityUnit_normalization`
  (`lem-trf-bundle-section-purity-unit-normalization`). This proves only the local
  normalization equation for the already specified unit mate. It asserts neither
  existence nor uniqueness of an orientation, nor its naturality or rank-zero
  comparison. Its source and complete proof in words are in its docstring and node.

The packet has three holes, compared with four original holes: two closed, one
added. The local normalization remains a dependency; the whole orientation result
is not claimed axiom-free. Existing holed dependencies are used as the stage
requires. There are no holes in definitions or private lemmas.

## No longer needed

Removed the following direct proof imports from the original module:
- `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`.
- `Sheaf.Paper.DegreeZeroDerivedMapGluing`.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`.
- `Mathlib.AlgebraicGeometry.Noetherian` (now a public import of the data module).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Mathlib.CategoryTheory.Adjunction.Basic`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
- `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`.

All original public imports are preserved through the publicly re-exported data
module. The proof no longer constructs orientations by gluing inverse maps:
`lem-pur-degree-zero-derived-map-gluing` is unnecessary for this route; only
equality of maps in one cohomological degree is used. The remaining naturality
and rank-zero plans now also use the new equality detector, after their local
comparison equations. Removed its obsolete top-level `tool_uses` approval from
the parent node. No new orientation gluing hole was added. Projective-completion
geometry and the arithmetic-only purity theorem are unnecessary for constructing
the unit-mate orientation; finite projection and the existing general-ring
integration-mate theorem suffice. The parent DAG retains the unfinished
naturality and rank-zero steps and their dependencies. Some removed direct imports
remain transitively required, so no whole module is claimed globally withdrawn.
No source-library declaration, module, or node is deleted. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan constructs an isomorphism by gluing local inverse maps before
identifying it with purity. This is unnecessary: the existing general finite-ring
integration-mate theorem constructs the isomorphism first, and only equality
needs local detection. It also avoids using the valuation-only purity statement
to establish the result for an arbitrary annihilator. The original statements
are retained; no false statement was encountered.

## New nodes

`def-trf-bundle-section-orientation-data` attaches the extracted, unchanged canonical
data and instances to the data module. Its definitions have no holes.

`lem-trf-bundle-section-purity-unit-isIso` records the proved construction of the
unit inverse-projection isomorphism and the invertibility of the actual unit mate.

`lem-trf-bundle-section-orientation-map-ext` records the proved affine-chart
equality detector via single-degree concentration and faithful cohomology
restriction.

`lem-trf-bundle-section-purity-unit-normalization` records the remaining local
normalization equation, with the specified source proof, as one separate item.

The parent node's proof and dependencies follow the new route. The definition
extraction change record is `coord/changes/A9-bundle-section-orientation-data.md`.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
