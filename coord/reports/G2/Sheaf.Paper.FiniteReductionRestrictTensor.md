## What changed

Restored `lean/Sheaf/Paper/FiniteReductionRestrictTensor.lean` from its quarantine
archive for rework after upstream sync 8bd69aede. The only Lean change is a local
`(J.W (A := ModuleCat A)).IsMonoidal` instance inside
`AlgebraicGeometry.FiniteReduction.extend_restrict_tensor`, supplied explicitly by
Mathlib's `GrothendieckTopology.W.monoidal`. This removes the default-20000-heartbeat
instance-search failure at `Sheaf.presheafToSheafCompTensorRightIso`.

The original signature, public imports, and complete composition of comparison
isomorphisms are preserved. No limits, upstream modules, definitions of scalars,
or consumers are changed. The node's proof text now records the elaboration repair;
its dependency list, Lean attachment and unit route remain intact.

Change record: `coord/changes/finite-reduction-restrict-tensor-monoidal-instance.md`.
The repair compiles; `#print axioms` of `extend_restrict_tensor` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

All four direct consumers were compiled individually from their unchanged quarantine
sources against the repaired sandbox module: `FiniteReductionDerivedExtension`
(16.4 s), `FiniteReductionFlatExtension` (10.5 s),
`FiniteReductionEtaleConstructibility` (13.7 s), and `ReductionOpenEtaleOrigin`
(32.9 s). All returned exit code 0 with no compiler warnings. The initial consumer
attempts preceded creation of the sandbox artifact and reported the missing archived
object file; after compiling the item into `.lbuild`, all checks passed.

## Proved and sorry left

This is a zero-hole definition repair. The archived item has 0 sorries and the
repaired item has 0 sorries. Holes closed: none. Holes added: none. Split off: none.
`AlgebraicGeometry.FiniteReduction.extend_restrict_tensor` is fully constructed,
with node `lem-pur-finite-reduction-restrict-tensor`; no sorry remains in any
delivered Lean declaration.

## No longer needed

None. Both existing public imports are retained, as is the proof dependency
`def-pur-finite-reduction-system`. No node or module is withdrawn or pruned.
The related consumers are quarantined rather than obsolete; their references
and the item's Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned compilation repair, not an unproved theorem. The archive
already contains a valid complete construction, but implicit synthesis of its
monoidal-localization instance now exceeds the typeclass-search limit after the
upstream sync. Explicitly applying the existing instance fixes that search without
changing the mathematics. The upstream algebra-based sheaf comparison was also
read; retaining the original arbitrary-ring-map construction avoids changing the
comparison maps or introducing an extra public dependency.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
