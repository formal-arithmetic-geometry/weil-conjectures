## What changed

Repaired the returned delivery `90d6e451e1`, whose landing failed over its old
base `e0d550965`. The current live module is absent in the shared snapshot and
server working tree; its rework archive is retained. Restore the archived
module with the reviewed explicit sheaf-module universe and definitionally
equal, explicitly typed pushforward presentation of the derived unit.

The current tree retired `Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`
in B4 landing `20261020T141302-L-2031820`. Consequently the returned packet
fails to resolve `RingTensorCohomology.mapHomologyIso_hom_comp`. Replace that
proof import with
`import all WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology`,
as in the upstream factorization module. This accesses the preserved, proved
private helper. Both existing theorem proofs and the public import remain
unchanged. No source-library file is edited.

The repaired module compiled on the server with `lcompile.py` in 26.4 seconds
without warnings. The generic scratch check recompiled in 2.3 seconds and proves the
pushforward functor and derived-unit equalities by `rfl`; no hypothesis or mathematical
conclusion changes. The DAG note and Lean signature preserve the reviewed
presentation and record the canonical source of the composition helper.

Dry run `08db094f0c` passed compilation, the axiom probe, and server preflight
on the refreshed delivery base; review class CODEX.

The source-only consumer check (`downstream.py --allow-missing`) reports zero
live consumers, consistent with the module's quarantine. Searches of the
quarantine also retain the two original consumers:
`AffineTildeCoefficientPushforwardHomologyCoordinates` uses the main theorem;
`AffineTildeDerivedTensorHomologyCoordinates` uses the unchanged inverse
comparison theorem. Their existing calls remain valid under the definitionally
equal presentation. No consumer adaptation or withdrawal is included.

Change record:
`coord/changes/B6-affine-tilde-pushforward-homology-abelian-universe.md`.

## Proved and sorry left

Compilation repair: zero holes before, zero holes after; zero holes closed,
zero holes added, zero split off. Complete proofs are preserved for:

- `AlgebraicGeometry.mapHomologyIso_inv_comp`.
- `AlgebraicGeometry.affineTildePushforwardHomologyFactorization`.

Both belong to `lem-pc-affine-tilde-pushforward-homology-factorization`.
No delivered declaration contains `sorry`.

## No longer needed

Removed the proof import of the retired
`Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`, replacing it by the
canonical source module's private proof import. The dependency node
`new-lem-pc-mixed-tensor-underlying-homology` already names that source module
and remains needed. The normalization public import supplies the statement's
objects and maps and also remains needed. No node or module is withdrawn or
pruned by this delivery; there are no new nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The return reports a stale delivery base. The current source remains in the
rework quarantine, so restoration uses that archive and preserves its Lean
attachment and dependencies. The retained proof import had become stale after
the separately reviewed retirement of its Sheaf provider. A new server compile
reproduced the unknown-helper error, and the canonical source import fixes it.
This packet includes that concrete compilation repair, beyond refreshing the
base. Delivery tooling constructs the new commit over current `sheaf-dag`.

The upstream factorization theorem uses different affine-tilde comparison
coordinates; replacing this module by that theorem would change its interface.
The existing direct homology-composition argument is retained. No additional
proof obligation is split off, and the original quarantine file is untouched.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
