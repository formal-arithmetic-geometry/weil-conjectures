## What changed

Changed only the proofs of `AffineZeroPurity.targetSourceRaw_left` and
`AffineZeroPurity.normalizationRaw_left` in
`Sheaf.Paper.AffineSpaceZeroSectionPurity`.

Both equalities compare the literal endpoints of existing canonical maps.
Case analysis on the dimension reduces the first to reflexivity. For the
second, unfold the existing `normalizationRaw` after case analysis, then use
reflexivity. This treats the empty affine tower and every positive dimension.
No definition, signature, import, attribute or node was changed.

## Proved and sorry left

Closed two of the five original holes, with no added holes:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.targetSourceRaw_left`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.normalizationRaw_left`.

Three existing holes remain, all attached to
`cor-pur-affine-space-zero-section-purity`, with their existing source and
natural-language proofs unchanged:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_untwisted`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity_baseChange`.

This is a partial proof delivery, not a decomposition. No new statements or
holes are introduced.

## No longer needed

None. No import or module was removed. The planned dependencies of the three
remaining statements are retained; proving these endpoint equalities does not
justify pruning them.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies exist, but two cannot currently be imported into this
item: `tools/import_direction.py may` reports that both
`Sheaf.Paper.CoordinateTowerNormalizationInduction` and
`Sheaf.Paper.CoordinateSectionProductRecursion` already reach
`Sheaf.Paper.AffineSpaceZeroSectionPurity`. The tower module directly publicly
imports the item. The product module reaches it through
`CoordinateSectionArrows` and `CoordinateSectionProjection`, among other paths.
These dependencies reuse this item's constructions, rather than its purity
results. Using them in this item's proofs will require moving the shared
constructions below both sides and adapting their imports. No such relocation
is included in this proof-only delivery.

The current blueprint also distinguishes the Cartier class from the signed
localization-boundary orientation: its normalization is 1 for products of
Cartier classes and (-1)^c for products of localization boundaries. The current
Lean constructions use the Cartier class. The two endpoint proofs are
independent of this distinction and do not change any normalization statement.

Validation: the complete changed module compiled through `lcompile.py` with
exit code 0 in 51.6 seconds. The source diff changes exactly the two proof
bodies above; every line is within 100 characters.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
