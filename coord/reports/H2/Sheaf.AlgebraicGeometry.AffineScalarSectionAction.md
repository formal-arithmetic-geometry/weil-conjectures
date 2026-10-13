## What changed

Replaced `affineScalarEnd_section_action` by a composition of the pointwise
tilde scalar calculation and general affine chart/slice scalar transport.
Added `TildeScalarSectionAction` and `AffineChartScalarTransport` as proof imports.
The original signature and public imports are unchanged.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.affineScalarEnd_section_action`.
Proved `AlgebraicGeometry.Scheme.tilde_scalar_section_action` by section
extensionality and localization fraction induction.
One new hole remains: `AlgebraicGeometry.Scheme.affine_chart_scalar_transport`
(node `lem-sc-affine-chart-scalar-transport`). This is a decomposition, not a
claim of a net hole reduction. The transport theorem concerns arbitrary
sheaves and uses the sectionwise scalar action as input; it is precisely the
second calculation of the original plan, independent of tilde localization.

## No longer needed

None from the original module. The two original dependencies supply the
definitions in its statement. The helper modules do not import
AffineFreeBasisGerms: the tilde calculation uses Mathlib directly; transport
uses DerivedHomMayerVietoris for `moduleRings` and Mathlib for the chart/slice
functors.
No stalk, regular-germ, or finite-free realization lemmas are used.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies define the functors but do not state either scalar
calculation. The localization part can be proved directly from Mathlib;
the structure-ring transport is isolated as the remaining calculation.
The local compiled library initially lacked AffineFreeBasisGerms, so an
unchanged sandbox copy was compiled for checking; it has no delivery edits.

## New nodes

`lem-sc-tilde-scalar-section-action`, in TildeScalarSectionAction: the proved
sectionwise localization calculation for arbitrary modules.

`lem-sc-affine-chart-scalar-transport`, in AffineChartScalarTransport: the
remaining chart/slice/direct-image structure-ring calculation for arbitrary
sheaves. Both statements include the empty-open and zero-ring edge cases.

## Second reading by H2

1. **Signatures and visible statements.** I diffed the delivered item module against the repository copy. The theorem signature of `affineScalarEnd_section_action` is byte-for-byte unchanged; only its proof and proof-only imports changed. The two added helper modules expose exactly the statements recorded in their new DAG nodes.

2. **Compilation and proof status.** I compiled all four sandbox modules with `lcompile.py`; they compile cleanly. The only remaining `sorry` is the named theorem `AlgebraicGeometry.Scheme.affine_chart_scalar_transport`, and it is the split-off theorem recorded by `lem-sc-affine-chart-scalar-transport`. There are no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions. The tilde theorem is proved by extensionality and localization-fraction induction.

3. **Statement review.** The tilde statement is the sectionwise scalar calculation for an arbitrary module and arbitrary open, including empty opens and zero rings. The chart-transport statement is the corresponding arbitrary-sheaf transport across restriction, the slice equivalence, and direct image. Both are strictly smaller than the original affine scalar-action target and are needed by its proof; neither duplicates an existing declaration found by repository and Mathlib searches.

4. **Route and pruning.** The proof follows the planned unit route: first the pointwise tilde calculation, then the chart/slice transport, then the original affine action. The original public import remains; the two helper imports are plain proof imports. No old proof dependency is unused beyond the definitions already needed by the target statement, so no additional node or module was pruned.

5. **DAG consistency.** The item node's `proof`, `proof_deps`, and `proof_origin` now name the two helper nodes and the affine scalar definition exactly as used in the Lean proof. Each helper theorem has a matching new node with source, proof route, search record, Lean declaration, and the item's chapter and unit. The unit's realized route is preserved.

I changed only the item proof/imports, added the two helper modules and their node files, and added this second-reading record. No statement or definition was changed.
