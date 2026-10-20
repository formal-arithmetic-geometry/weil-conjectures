## What changed

Restored the assigned quarantined module and repaired the proof import for
`locallyFinitelyPresented_of_isZero`: the helper now lives in the synced
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`
module, which must be imported with `import all` for its private helper.
All original public imports, declarations, signatures and proof bodies are preserved.
The existing DAG attachment and all proof dependencies are preserved. The change
record `coord/changes/A3-lfp-tensor-single-private-import.md` documents the sole
quarantined consumer, which needs no adaptation. The restored file compiles through
`lcompile.py` in 20.3 seconds with exit code 0.

## Proved and sorry left

This is a zero-hole compile repair. The restored archive already had complete proofs
of `integral_tensor_single` and `lfp_tensor_single`. Closed 0 direct holes, added 0,
split off 0, remaining 0. No proof is claimed as newly closed by the import repair.

## No longer needed

The private `import all` of the upstream
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` is replaced by
private-name access to the relocated helper module. The upstream module remains a
public import, and all mathematical dependencies and nodes remain needed. No modules
are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The current rework entry accurately records the post-sync missing private identifier.
The archived proof imported private names from their pre-sync location. No change to
the mathematical statement, the proof route, the unit route or the DAG is necessary.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
