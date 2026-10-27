## What changed

Restored `lean/Sheaf/Paper/CommonStagePullbackRepresentativeLinearity.lean`
from the source preserved at
`quarantine/Sheaf/Paper/CommonStagePullbackRepresentativeLinearity.lean`.
The G1 rework claim was renewed before this restoration delivery.

The archived proof failed in the global build at its final `simpa only [ht] using hm`.
The repaired proof explicitly transports the specified representative-map formula
along the equality obtained by applying `ofHom` to the finite-stage scalar identity.
The final step is now `hm.trans (heq_of_eq ht)`. The canonical stage-linear
instance, theorem signature, public imports, and all DAG attachments and
dependencies are preserved. The repaired module compiled without warnings in
34.0 seconds through `lcompile.py`.

## Proved and sorry left

This is a restoration and proof repair with zero existing holes, zero holes closed,
and zero holes added. Both `commonStageRepresentativeLinearity_stageLinear` and
`commonStageDerivedPullback_map_smul_of_linear` have complete bodies. No theorem is
split off and no `sorry` remains in the delivered module.

## No longer needed

None. All three declared proof-dependency nodes remain in use:
`lem-weil-integral-constructible-linear`,
`def-weil-derived-pullback-tensor-hom`, and
`def-weil-algebraically-closed-coefficients`. No import, declaration, or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The return of delivery `3ec6c199aa7` states that the item was moved to quarantine
after its delivery base. This packet restores the complete archived module at its
original Lean path, retaining its Lean attachment and dependencies, and repairs
the final equality transport reported in
`coord/build-errors/Sheaf.Paper.CommonStagePullbackRepresentativeLinearity.txt`.
It does not delete the quarantine archive or replace the module with a stub.
The DAG statement and mathematical proof route remain unchanged.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
