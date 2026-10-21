## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsPreoverlap.lean`
from the quarantine path recorded in `coord/rework.tsv`. The archive already
contains a complete proof of
`AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap`. The restored
file is byte-identical to that archive: its signature, visibility, public
imports, private proof imports, docstring and proof are preserved.

The proof obtains the two short exact rows, strict row map, six vertex
isomorphisms and normalized equations from
`relativeMV_direct_image_rows_core`, then applies
`relativeMV_direct_image_rows_mates` and packages the witnesses. Both
dependencies are present and proved in the current library. No additional
geometric construction or intermediate theorem is needed.

Validation: the item compiled cleanly in 7.4 seconds, and its original
archived direct consumer `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows`
compiled unchanged in 6.1 seconds. The scratch validation compiles both
sources together so the consumer uses the restored item, rather than a
stale published artifact. A separate axiom probe checks both declarations.
Both axiom lists contain only `propext`, `Classical.choice` and `Quot.sound`.
The consumer and probe are validation files only, not delivery changes.

Change record:
`coord/changes/B4-relative-mv-direct-image-rows-preoverlap-restoration.md`.

## Proved and sorry left

The restored theorem
`AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap`
(node `lem-pc-relative-mv-direct-image-rows-preoverlap`) has a complete proof.
The quarantine baseline contains zero holes. Holes closed: zero. Holes
added: zero. Holes remaining in the item: zero. No statements were split off.
This is a restoration of a missing proved module, not a new proof closure.

## No longer needed

None. Both proof imports are used, and the two public imports supply the
statement's interfaces. No node, module, declaration or DAG edge is removed.
The existing Lean attachment and the two proof dependencies stay unchanged.

The quarantined parent still cites this theorem in Lean and in its node's
proof dependencies. Its absence from the live source tree does not justify
withdrawal. The suggested root-specific Cech route would require a separate
replacement argument and parent updates; this restoration makes no such
pruning claim. The unit statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The route note describes an earlier unfinished geometric obligation. The
current quarantine archive already proves it from the row-core and mate
interfaces, and the assigned rework is the module's missing live path after
the cluster-restore rollback. The old B4 upstream-sync notice does not
authorize deleting the archive or its dependencies. No statement correction
or definition repair is required.

Loogle confirmed `Equiv.symm_apply_apply`; LeanFinder returned generic
Mayer--Vietoris sheaf machinery, with no shorter replacement for the existing
two-interface proof. The proof's cancellation has no nonemptiness or
distinctness condition on the opens, so empty and repeated opens require
no additional case split at this assembly step.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
