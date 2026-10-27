## What changed

Replaced the hole in `WeilConjectures.CompactSupportFiniteProjection.properComponent_transpose`
by a calculation through the faithful fixed coefficient coordinate functor. Its original
statement and public import are unchanged. Three proof imports supply separate steps.
`FiniteProjectionFixedCoordinates` constructs the coordinate functors, fixed direct
adjunction, tensor comparisons and normalized direct-image comparison, and proves the
pullback comparison and tensor naturality API. All data are composites of existing maps.

The assigned proof combines the three coordinate identities using the published scalar
projection-counit formula, naturality, tensor functoriality and faithful reflection.
Private generic category lemmas keep the counit and tensor cancellations from unfolding
large derived constructions. No existing module besides the assigned item is changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CompactSupportFiniteProjection.properComponent_transpose`
(node `lem-sf-finite-proper-projection-transpose`). This is a decomposition, not a complete
proof of the transitive dependency closure. The assigned proof compiled in 26 seconds
before removal of unused private helpers and linter cleanup. Delivery checks recompile it.

Added exactly three holes, each the entire proof of a public theorem in its own module:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization`
  (`lem-sf-finite-proper-projection-fixed-realization`) identifies the projection before
  applying a pullback or taking a supplied adjunction transpose.
- `WeilConjectures.CompactSupportFiniteProjection.directCounit_fixed_realization`
  (`lem-sf-finite-direct-counit-fixed-realization`) compares the two counits for every
  morphism, with no properness, tensor, projection or finite Tor assumption.
- `WeilConjectures.CompactSupportFiniteProjection.pullbackTensor_fixed_coordinates`
  (`lem-sf-finite-pullback-tensor-fixed-coordinates`) expands the specified pullback/tensor
  comparison and cancels coefficient units; it contains no projection map or counit.

The assigned module and coordinate definitions module contain zero holes. Each new
statement is a distinct, strictly partial step of the original argument. Their docstrings
and nodes give complete proofs in words. The attempted direct proof of the third step
reduced to definitional presentation comparisons, but elaborating the final derived
functor comparison exceeded the file limit; that calculation is explicitly split off.

## No longer needed

None. No original import was removed, and no module or node is withdrawn. The original
`def-exchange-projection`, `def-fix-six-functor-datum`,
`def-sf-constructible-projection-mates` and `def-sf-finite-partial-pullback-tensor`
remain needed directly or by the normalization statements. The unit's proper-factor
route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was corrected. The original plan names normalization fields
but has no published theorem identifying the prescribed derived coefficient comparisons
with the fixed direct counit, or cancelling the identity-open compactification in the
proper projection. These are the first two isolated obligations. The third isolates the
explicit pullback/tensor coordinate calculation.

The rework table has a quarantine entry for the item, but the current live source exists
and imports `FinitePartialPullbackTensor`. This delivery preserves its attachment and
replaces its proof rather than withdrawing it. No change record is needed: no existing
public statement, definition, attribute or public import changes.

## New nodes

`def-sf-finite-projection-fixed-coordinates`, attached to
`Sheaf.Paper.FiniteProjectionFixedCoordinates`, records the full inclusion/inverse
coefficient functor, its faithfulness, the fixed direct adjunction, tensor and direct
comparisons, and the proved naturality API. No hollow data or arbitrary witness is used.

`lem-sf-finite-proper-projection-fixed-realization`, attached to
`Sheaf.Paper.FiniteProperProjectionFixedRealization`, records proper projection realization.
It uses proper normalization independently of the supplied adjunction comparison.

`lem-sf-finite-direct-counit-fixed-realization`, attached to
`Sheaf.Paper.FiniteDirectCounitFixedRealization`, records derived counit normalization
for an arbitrary morphism, independently of tensor and projection.

`lem-sf-finite-pullback-tensor-fixed-coordinates`, attached to
`Sheaf.Paper.FinitePullbackTensorFixedCoordinates`, records the separate pullback/tensor
coordinate expansion and coefficient-unit cancellation.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
