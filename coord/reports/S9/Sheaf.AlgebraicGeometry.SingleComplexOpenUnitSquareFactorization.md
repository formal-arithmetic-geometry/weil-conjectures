## What changed

Retire the quarantined module
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization` in favor of
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization`,
as explicitly assigned by the retirement handoff. `deleted.txt` lists its original
Lean path. The archive under `quarantine/` is untouched.

Redirect `lem-pc-k3-open-unit-square-factorization` to the official twin. Its
public theorem signature is byte-identical to the quarantine and the node's
recorded signature. Update the proof description to reflect that `derivedPullback`
is already globally irreducible; the twin's proof and dependency are preserved.
Change record: `coord/changes/s9-open-unit-square-retirement.md`.

The listed Sheaf consumer is already absent. Its live upstream replacement,
`WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization`,
already imports the twin and applies the same theorem name. No consumer edit is
necessary. Its parent DAG node already points to that upstream consumer and
continues to cite this node. No unit statement or step is bypassed.

For the rework verification, copied the current quarantine to its assigned sandbox
module path and removed only `derivedPullback` from the local irreducibility
annotation. Fresh `lcompile.py --all` succeeded without warnings: the repaired
item compiled in 23.2 seconds and the unchanged upstream consumer in 0.1 seconds.
Their checked sources are preserved under `scratchpad/`; the final packet
withdraws the copy. The earlier repair is also retained there.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Holes left: 0. Split off: 0.
This is the assigned compilation repair and retirement, with no decomposition.

`AlgebraicGeometry.singleComplexOpen_unit_square_factorization` and its private
`square_factorization` helper have complete proofs in the quarantine, repaired
copy, and official twin. The checked consumer theorem
`AlgebraicGeometry.singleComplexOpen_pullback_counit_homotopy_factorization`
also has no textual proof hole. No theorem is replaced by `sorry`.

## No longer needed

Withdraw `Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization`.
No current module under either library root or the quarantine imports it. Its
former Sheaf consumer is already absent, and the live upstream consumer imports
the official twin. No live consumer import needs changing.

Keep `lem-pc-k3-open-unit-square-factorization`, now attached to the twin, and
its dependency `lem-pc-open-pinned-counit-unit`. Keep the parent's dependency on
this node and the unit route. No mathematical lemma or unit step is pruned.
Historical `created.item` and blueprint provenance are preserved.

## Where the brief, the DAG or earlier work was wrong

The consumer list predates the upstream sync: both listed Sheaf paths are absent
from the live library. The current parent is the official upstream consumer;
its import and theorem application already use the twin. The remaining defect
is the quarantined copy and its stale DAG attachment.

The previous attempt was blocked because `deliver3.py` refused a deletion of an
already-absent quarantined module. The current launcher explicitly accepts a
path backed by `quarantine/`, so that diagnosis is obsolete. This resumption
started with the required dry run, which reached server preflight. The final
packet retains the required deletion entry and is checked again after updating
this report. No launcher script or gate metadata was edited.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
