## What changed

Filled four of the seven existing proof holes in
`Sheaf.Paper.PurityCompositionCompatibleDncCharts`, preserving every declaration signature
and every definition body. The affine-cover theorem is placed after the existing
composite-chart theorem so it can reuse its etaleness assertion.

- `composition_compatible_affine_charts`: install the three actual field structure maps,
  apply `AffineDifferenceTower.exists_compatible_charts`, retain the specified finite-type
  restrictions, and use `composition_compatible_tangent_normal` for the ordered composite.
- `compatibleNormal_condition`: cancel the normal-coordinate isomorphisms using
  `chartNormalCoordinateMap_spec`, identify the two normal projections, and use the
  affine-space block projection and base-map equations.
- `compatibleNormalSplitting_spec`: paste the standard ordered block pullback square with
  the affine-space base-change square, transport it through the three specified normal
  coordinate isomorphisms, and identify its canonical pullback isomorphism with the
  constructed splitting. Cancellation of the coordinate maps proves the projection and
  both zero-section equations.
- `compatibleDelta_etale_restriction`: apply
  `chartDiagonalDelta_coordinate_identity` to the supplied centred chart, then use
  functoriality on the identity isomorphism.

Validation: the final pruned module compiled cleanly through `lcompile.py` (16.5 seconds,
exit code 0). Every existing declaration signature is unchanged.

The argument has no nonemptiness or positive-rank condition. In particular both block
pullback squares and the zero-section computations apply when either rank is zero.

## Proved and sorry left

Closed four existing holes, with full namespace `WeilConjectures.PurityFiniteSetting`:

- `composition_compatible_affine_charts`
- `compatibleNormal_condition`
- `compatibleNormalSplitting_spec`
- `compatibleDelta_etale_restriction`

Added zero holes and split off zero statements. Three existing holes remain unchanged:

- `compatibleNu_etale_restriction`
- `composition_compatible_tangent_normal`
- `composition_compatible_dnc_charts`

All seven declarations belong to `lem-pur-composition-compatible-dnc-charts`. This is a
partial delivery. The affine-cover and normal-bundle proofs reuse the existing composite
chart assertion of `composition_compatible_tangent_normal`; that theorem is still open.
The existing chart normalization, affine difference tower and section-pasting dependencies
also remain proof obligations elsewhere. No claim of axiom-free transitive closure is made.

## No longer needed

Removed the following unused private imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.Kaehler.Basic`
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
- `Sheaf.AlgebraicGeometry.RelativeTangentBundle`

The first four are redundant with the retained public prerequisites and add no lemma
used by the new proofs. The relative tangent scheme is not used by the derivation-based
statement or by the independently constructed normal-coordinate maps, so the node's
Step 4 and proof dependencies no longer cite `pur9-dg-def-tangent`.
No module is withdrawn. No source-library declaration is removed. All other declared
node dependencies are retained for the three unfinished theorem proofs.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing normal-coordinate specification and
standard affine-space pullback square suffice for the normal-bundle conclusions; these
conclusions do not require a separate construction of the relative tangent scheme.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
