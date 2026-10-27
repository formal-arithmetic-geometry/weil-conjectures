## What changed

Replaced the hole in
`WeilConjectures.PurityFiniteSetting.affineDiagonalNormalCoordinates_spec`
by a complete transport argument. It factors the actual coordinate map through
`q.hom`, the intrinsic relative-Spec coordinate map, and the tower isomorphism.
The first equation of `ReesConeNormalized` and `purityNormalProjection_eq` identify
the base projection. `AffineSpace.comp_homOfVector` proves the factorization;
composition proves invertibility and `homOfVector_over` proves the projection equation.
Existing signatures, definitions, and the unit route are unchanged. Local irreducibility
attributes keep the cone coordinate constructions behind their interfaces when
elaborating the later derived-map statements. A profiling compile identified
expensive unfolding in those statements; the full module then compiled in 48.3 s.

Added the proof import `Sheaf.Paper.AffineDiagonalGradedCoordinates`, containing
only the remaining polynomial associated-graded coordinate calculation. Its statement
has no Rees comparison, normalization predicate, integration, or DNC arrow. Its
docstring and node give the full affine calculation and localization/gluing argument,
including rank zero and empty bases. Updated the parent node's step 5 and dependencies.

## Proved and sorry left

One original hole is replaced by a complete Lean proof from one strictly smaller
statement: `WeilConjectures.PurityFiniteSetting.affineDiagonalNormalCoordinates_spec`.
This is a decomposition, not a net hole reduction: one hole closed and one added.
The original module had five holes; four remain there. Including the new module,
five holes remain in this packet.

Unchanged holes (all attached to `lem-pur-affine-diagonal-integration-orientation`):

- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_translation`
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_exponent`
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegration_zero`
- `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegrationOrientation`

Added hole:

- `AlgebraicGeometry.PurityNormalBundle.affineDiagonalGradedCoordinates_isIso`
  (`lem-pur-affine-diagonal-graded-coordinates`).

The parent proof now supplies the actual comparison transport and projection equality;
the new hole is confined to polynomial coordinates on the intrinsic graded cone.
No arbitrary data is chosen from the new theorem: it asserts `IsIso` for an explicitly
constructed map. The existing degree-one lifts remain the uniquely determined
representatives of the difference functions.

## No longer needed

No original import, node, or module is pruned: the four remaining integration holes
still have their planned dependencies, including `PurityDncComparisons` and the
standard-pair unit route. The new module imports only `AffineTraceTower` and
`ReesConeNormalization` for its signature; it does not import the integration stack.
No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement change or dispute. The old step 5 combines two distinct
pieces: the polynomial associated-graded coordinate calculation and transport through
the normalized Rees isomorphism. The latter now has a complete Lean proof; the former
is the new statement. The existing extended-Rees chart theorem
`normalConeChartRingIso` does not directly identify the intrinsic relative-Spec map
appearing here. The new statement isolates precisely that missing affine calculation.

## New nodes

`lem-pur-affine-diagonal-graded-coordinates`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-diagonal-graded-coordinates.json`,
states the intrinsic coordinate-map isomorphism. Its source is the current blueprint's
normal-bundle calculation in the proof of `lem-pur-projection-purity-agreement`,
expanded by the parent node's step 5. The node records the three search kinds,
affine-chart proof, localization compatibility, rank-zero and empty-base checks,
and the verbatim Lean signature. No existing definition or statement changes,
so no change record is required.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
