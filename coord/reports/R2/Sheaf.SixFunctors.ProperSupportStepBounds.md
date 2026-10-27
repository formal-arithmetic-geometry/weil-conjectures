## What changed

Proved `WeilConjectures.IntegralSystemRealization.properSupportStep_bounds` with
its original signature and public imports. All supporting declarations added to
`Sheaf.SixFunctors.ProperSupportStepBounds` are private and completely proved.
Updated `lem-sf-proper-support-step-bounds` to record the implemented argument.
No definition, public interface, target, or adopted source-library file changed.

The proof has four parts. A uniform relative fibre-dimension bound and the
existing `ProEtale.finite_bound` helper give common cohomology and Tor intervals
without separatedness assumptions on the structure maps. Normalization follows
from the input universal property, finite compact-support scalar comparison, and
the native system transition square; uniqueness of adjoints identifies the native
image with the specified `Operations.push`. Full faithfulness lifts the actual
output transitions to bounded etale antecedents, giving precisely the two squares
required by `Origins`. Finally the completed direct-image reduction comparison
and integral direct-image constructibility prove the independent integral claim.

The normalization argument generalizes the existing proved private
`compactSupportSystem_normalized` argument from integral reductions to an
arbitrary normalized system with constructible levels. Its restriction comparison
helpers are reused by a private proof import, rather than restated. The chosen
etale antecedents are determined up to isomorphism by full faithfulness and the
specified realization, not arbitrary witnesses of mere existence.

Validation: the delivery source compiled cleanly through `lcompile.py` in
37.1 seconds (exit 0), within the 60-second limit. Static comparison confirmed
the theorem signature and both public imports are unchanged; the updated node
changes only `proof`, `proof_deps`, and `proof_origin`, with no dependency cycle.
The delivery tool runs the independent compile and preflight before pushing.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.IntegralSystemRealization.properSupportStep_bounds`
(node `lem-sf-proper-support-step-bounds`). Original holes: 1; remaining holes: 0;
new holes: 0; split-off statements: 0. Every private helper is fully proved.
The proof uses existing named declarations, including the still-open
`WeilConjectures.compactSupportNativeSystemTransition`; no imported obligation is
claimed to have been closed by this delivery.

## No longer needed

No original import was removed: both public imports support the unchanged
statement. No module is withdrawn.

The item's former direct proof dependencies no longer needed are:

- `lem-sf-cartesian-open-adjunction-restriction`
  (`Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction`): the proved finite-bound
  helper applies globally, so no affine restriction is needed.
- `lem-sf-finite-cover-ctf-locality`
  (`Sheaf.SixFunctors.FiniteCoverCTFLocality`): the relative fibre-dimension bound
  and the global helper already give one interval.
- `lem-fix-proper-etale-origin-scalar-isomorphism`
  (`Sheaf.Paper.ProperEtaleOriginScalarIsomorphism`): replaced by the existing finite
  compact-support scalar comparison and native system coefficient square.
- `lem-weil-pbc-normalized-etale-origin-witnesses`
  (`Sheaf.Paper.NormalizedEtaleOriginWitnesses`): `Origins` requires the adjacent
  transition lifts and their squares, which full faithfulness supplies directly.

These are removals from this item's proof route; other consumers may still need
them. The arbitrary-finite-ring bound, finite-ring derived origins, and both
integral direct-image dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The planned affine-cover detour is unnecessary: the public compact-support bound
has stronger geometric hypotheses, but its existing proved private `finite_bound`
helper has exactly the weaker hypotheses needed here. Also `Origins` does not ask
for the stronger normalized-origin cocycle package; lifting each actual adjacent
transition and checking its two squares suffices. There is no statement dispute
or change of meaning. The empty scheme, zero levels, and equal coefficient indices
are covered by the same bounds and the all-pairs normalization argument.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
