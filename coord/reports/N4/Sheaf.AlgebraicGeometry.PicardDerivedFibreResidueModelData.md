## What changed

Restored `Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData` from its
assigned quarantine archive. Repaired the universe inference failure in the
private `restrict_model_local` helper with explicit `overFunctor.{v}` at all
three occurrences. The public theorem
`AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data` and all public
imports are byte-identical to the archive.

Replaced the longer affine-spectrum primality argument with
`RingHom.ker_isPrime`. Removed the unused finite-free residue-model proof import
and updated the existing node's proof route and dependencies to match the Lean.
The local strictly perfect models already follow from `IsPerfect`.

Validation: the untouched archive failed with the recorded universe constraint;
the repaired module compiled cleanly in 29.5 seconds through `lcompile.py`.
An explicit textual check verified the complete theorem signature and public
imports against the archive, and found zero occurrences of `sorry`.
The user scan includes archived parents, and the unit route is retained.

The restored module also compiled into the consumer sandbox in 29.0 seconds;
the unchanged archived `PicardDerivedFibreResidueBridgeCore` compiled in
29.9 seconds. The first `PicardDerivedFibreResidueBridge` check reached the
60-second limit. A profiling run of that archived consumer then compiled in
49.2 seconds (28 seconds kernel checking; approximately 10 seconds for its two
large theorem applications). No consumer interface or proof edit is included in
the delivery. The final unprofiled bridge retry again reached 60 seconds;
its successful profiled check establishes compatibility, but that archived
consumer still has a separate performance concern. The assigned module itself
has two clean checks under 30 seconds.

Change record:
`coord/changes/N4-picard-derived-fibre-residue-model-data-restoration.md`.

## Proved and sorry left

This is a zero-hole compile repair: zero holes before, zero holes after, zero
holes closed, zero holes added, zero split off. There are no remaining holed
declarations in the delivered module or any added module.

The restored complete theorem is
`AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data`
(node `new-picard-derived-fibre-residue-model-data`). Its three private helpers
also have complete proofs. No extra closure of a hole is claimed.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
and its node dependency `lem-sc-perfect-finite-free-residue-model`. No fibre
ranks or finite-free residue models occur in this argument: the needed strictly
perfect models are precisely the witnesses in `IsPerfect`. This removes that
dependency from this proof, without withdrawing its module or any source-library
declaration. No other module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from `lean/` because it is quarantined, not because
it was withdrawn. Its archive is retained and its original Lean attachment is
preserved. The archived source has zero holes; its actual defect is the universe
inference failure in the restriction helper. The previous node proof overstated
the use of finite-free residue models even though the archived Lean already
extracted strictly perfect models directly from the definition of perfectness.
The node now follows the actual proof and handles the empty finite family by
its intersection being top. No mathematical statement or unit route changes.

Searches run through `msearch.py`: LeanFinder for simultaneous affine local
strictly-perfect models (only general affine-neighbourhood results); Loogle for
`RingHom.ker_isPrime` (the exact primality lemma); grep for common affine models
(no hits in that service). Local `rg` found the upstream two-object
`perfect_common_affine_models`, whose restriction argument agrees with this
finite-family construction, and the definition of `IsPerfect` itself. No new
lemma or node is needed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
