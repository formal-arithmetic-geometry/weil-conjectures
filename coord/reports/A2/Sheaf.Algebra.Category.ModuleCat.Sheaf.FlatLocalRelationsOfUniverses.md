## What changed

Restored the quarantined item module from its preserved source and repaired
`SheafOfModules.tensor_mono_locallyInjective` (private): replace the implicit
`(toSheaf _).map_mono` invocation with
`preserves_mono_of_preservesLimit (toSheaf _)`. This uses the existing finite-limit
preservation instance directly, avoiding the failed search for the functor's
`PreservesMonomorphisms` instance after the FlatOnSite public dependency changed.
The full module compiled cleanly through lcompile.py. The tensor comparison
naturality proof also explicitly reduces only functor mapping and tensor functor
definitions, avoiding an expensive unrestricted definitional-equality check.
Both public
declarations, all definitions, all signatures, visibility, imports and the DAG
proof route are unchanged. No consumer adaptation or definition change is needed.

## Proved and sorry left

This is a quarantine compile repair with zero original holes: proved 0 of 0
sorries; added 0; remaining 0. The restored declarations
`SheafOfModules.local_equationalCriterion_of_isFlatOnSite` and
`TensorProduct.exists_relations_with_coefficients` retain their complete proofs
and attachment to `lem-weil-pbc-flat-local-relations-universes`.

## No longer needed

None. All original imports and declared proof dependencies remain in use. No
modules or nodes are withdrawn, including quarantined consumers.

## Where the brief, the DAG or earlier work was wrong

The assigned rework is the compile failure recorded in coord/rework.tsv, at the
old line 308. The implicit preservation-of-monomorphisms search failed despite
the available finite-limit preservation instance. An explicit application of
Mathlib's preservation-of-pullbacks theorem repairs that step without altering
its mathematical argument. There is no return entry for this item in the current
A2 return file. No new nodes or statements were needed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
