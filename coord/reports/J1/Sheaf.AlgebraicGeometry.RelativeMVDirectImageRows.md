## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRows.lean`, as
assigned by `coord/rework.tsv`, with its complete archived public signature,
visibility, universe parameters and docstring unchanged. The signature
exactly matches the existing DAG Lean attachment.

The proof now obtains the resolved rows and three normalized equations
directly from `AlgebraicGeometry.relativeMV_direct_image_rows_core`. Each
component follows by `Equiv.symm_apply_apply` and cancellation of the target
vertex isomorphism. This keeps the same witnesses, short-exactness proofs,
and global, middle and overlap mate identities with fewer dependencies.
Both public imports remain; the two archived private imports are replaced
by `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore`.

Updated the existing node's proof, proof dependencies and proof origin to
match this argument. Its statement, attachment, source and unit route remain
unchanged. No new declaration, definition, node or axiom was introduced.

Change record: `coord/changes/J1-relative-mv-direct-image-rows-restoration.md`.

## Proved and sorry left

This is restoration of an already proved, quarantined module: 0 of 0 holes
closed; 0 holes added; 0 split off; 0 remain.
`AlgebraicGeometry.relativeMV_direct_image_rows` has a complete shorter proof.
There are no declarations left with `sorry` and no added modules or holes.

The final restored module compiled cleanly against the published server build
in 8.0 seconds. Compiling it with its byte-identical archived direct consumer
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison` succeeded
in 8.5 and 30.2 seconds respectively. Both final declarations report exactly
`propext`, `Classical.choice` and `Quot.sound` under `#print axioms`.
Signature equality, the 100-character Lean line limit and the restricted node
field changes were checked explicitly. All compiles used `lcompile.py`.

## No longer needed

Removed the private imports of
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap` and
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsOverlapMate`.
Their nodes `lem-pc-relative-mv-direct-image-rows-preoverlap` and
`lem-pc-relative-mv-direct-image-rows-overlap-mate` are no longer proof
dependencies of this item. The transitive wrapper
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsMates`, node
`lem-pc-relative-mv-direct-image-rows-mates`, is also unnecessary for this
proof. These wrappers only unpack the row-core or cancel equivalences and
isomorphisms; the new proof performs the cancellations directly.

All of the row-core's substantive construction dependencies remain needed.
The wrapper modules and DAG nodes are preserved, with no withdrawal or
source-library deletion. Searches of live and quarantined sources find no
other callers of the two removed direct imports; Mates is used by Preoverlap.

## Where the brief, the DAG or earlier work was wrong

The missing live source is a cluster-restore rework, not a mathematical
withdrawal. The archive already contains a complete proof with zero holes.
The old DAG second-step prose attributed an open-counit calculation to the
overlap-mate theorem; that theorem only cancels a target isomorphism. The
row-core's normalized equations contain all the needed comparison data, so
all three wrapper steps can be replaced by elementary cancellation without
changing the unit route or the result.

An initial compile of the verbatim archive found an obsolete published
preoverlap artifact importing the former `Sheaf` base-change module alongside
its `WeilConjectures` replacement. A scratch set containing the current,
unchanged dependency sources, the archived item and its original consumer
compiled cleanly (item 7.5 seconds; consumer 31.2 seconds), with only
`propext`, `Classical.choice` and `Quot.sound` in both axiom lists. The shorter
proof independently compiles against the published build using its existing
row-core artifact. No dependency source is modified or redelivered.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
