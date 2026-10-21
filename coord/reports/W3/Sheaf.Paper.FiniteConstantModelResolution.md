## What changed

Restored lean/Sheaf/Paper/FiniteConstantModelResolution.lean byte for byte from
quarantine/Sheaf/Paper/FiniteConstantModelResolution.lean, as required by its
coord/rework.tsv assignment. This restores the actual scalar constructions,
model functors, and complete two-term finite-free resolution proof at the path
still named by its two DAG nodes. No declarations, imports, or node fields were
changed relative to the archive. No archive was removed.

Change record: coord/changes/W3-restore-finite-constant-model-resolution.md.

The restored module compiled cleanly against the published library in 9.3 s.
In an isolated scratch overlay, the restoration compiled in 10.5 s and both
unchanged direct consumers compiled: ConstructibleInternalHomContinuity in
5.4 s and InternalHomDualConstructibleModels in 9.0 s. Consumer copies and probe
files are only in scratchpad/, outside the delivered lean/ tree.

## Proved and sorry left

This is a zero-hole quarantine restoration, not a newly proved or decomposed
hole. Original holes: 0. Holes closed: 0. Holes added: 0. Holes left: 0.

The archived complete proofs are preserved for scalarAction_laws,
scalarMap_linear, scalarToContinuous_isMonHom, constantScalars_commutative,
and finite_constant_model_two_term_free_resolution, all in namespace
AlgebraicGeometry.ProEtale.FiniteConstantModel. The real construction bodies
and all proved private helpers are preserved. No new statement was split off.
The five public theorem axiom probes show only propext, Classical.choice, and
Quot.sound, including the final two-term resolution theorem.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies were pruned.
Both original DAG attachments and the canonical coefficient constructions
remain needed by the archived direct consumers and are restored unchanged.

## Where the brief, the DAG or earlier work was wrong

The live Lean path is missing because the module was quarantined after a
cluster restore, as the rework row records. This is not an absent mathematical
statement or authorization to withdraw it. The archive already compiles with
complete local proofs, and its restoration repairs the missing source.
There is no statement, definition, or unit-route correction in this packet.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
