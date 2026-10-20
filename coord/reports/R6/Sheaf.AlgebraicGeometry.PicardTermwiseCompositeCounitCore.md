## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardTermwiseCompositeCounitCore.lean`
as a public reexport of the proved upstream counterpart, and pointed the existing
node's Lean attachment at
`WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounitCore`.
The theorem `AlgebraicGeometry.Scheme.picard_termwise_counit_composition` has
exactly the same signature and complete proof in that upstream module. The
source module and its consumer are unchanged. The termwise-model public import
remains available transitively. No consumer adaptation is required.

Repair of return C-549a2 (returned head `549a245ef5`): reconciled the retained
packet with current `sheaf-dag` at `f5dbb5f7608`. The current item remains absent
from `lean/` and preserved at the quarantine path listed in `coord/rework.tsv`.
Its current archived source is byte-identical to the retained original; its
public theorem statement and proof are byte-identical to the current upstream
theorem. Thus the restoration still repairs the recorded redundant local
`irreducible` attribute without discarding an intervening theorem change. No
archive is deleted and no empty-module withdrawal is requested. The delivery
tool rebuilds the commit on current `origin/sheaf-dag`, replacing the stale
`d92f73d8e` base responsible for the failed landing.

The restored module compiled on the server through `lcompile.py` in 1.3 seconds
against the current library. The separate axiom probe is recorded below. The
previous reviewed packet's dry run passed; this repair reruns compilation and
preflight on the refreshed base before pushing.

The duplicate merge and attachment change are recorded in
`coord/changes/R6-picard-termwise-counit-upstream-reducibility.md`.

## Proved and sorry left

This is a quarantined build repair with zero original proof holes.
`AlgebraicGeometry.Scheme.picard_termwise_counit_composition`
(node `lem-sc-picard-termwise-composite-counit-core`) is supplied by its identical,
proved upstream declaration. Holes closed: none (0 of 0). Holes added: none.
Holes remaining in the restored module or its upstream counterpart: none.
No theorem is split off. The upstream theorem's axiom probe reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the duplicate local theorem and its four private helpers
`invert_factorization_map`, `normalize_counit`, `pushforwardCongr_refl`, and
`tensor_composition_inv`. Their original versions remain in the upstream module
with the same proof. The duplicate's local attributes and elaboration options
are consequently unnecessary.

Replaced the direct public import
`WeilConjectures.AlgebraicGeometry.PicardTermwiseModels` by the public import of
`WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounitCore`; the former
remains available transitively. No mathematical dependency, DAG node, or module
is pruned from the import closure. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with a hole or an assigned repair.
This item is the latter: `coord/rework.tsv` records its quarantine and the
redundant-attribute compiler error. Its source is under `quarantine/Sheaf/`,
not currently under `lean/Sheaf/`. The existing proof and DAG route are complete.
The exact upstream counterpart supplies the same declaration and proof. Only
the node's Lean attachment changes; its mathematical statement, proof and
dependencies stay.

The prior packet passed independent review but failed landing because another
landing changed the item after its delivery base. This retry uses the current
quarantine and upstream source and delivers on the refreshed main branch. It
restores the nonempty public reexport rather than treating quarantine as evidence
that the item is unnecessary.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
