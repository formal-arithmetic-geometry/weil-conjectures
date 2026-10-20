## What changed

Restored Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility from the archive
identified in coord/rework.tsv. Replaced its public import of the withdrawn
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations with the adopted
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations provider.
The upstream provider is already the definition node's recorded Lean attachment.
Every declaration, signature, attribute, docstring, and proof body is preserved
verbatim. No source-library file changes.

The untouched archive reproduces the recorded unknown-identifier errors for
scalarCohomology and scalarCohomologyCup through lcompile.py (4.8 seconds).
The repaired module compiles cleanly (6.5 seconds). A separate consumer importing
only the repaired module publicly can restate its full public signature and apply
scalarCup_moduleCup_compatibility: the two-file check passes in 7.4 and 3.5 seconds.
The consumer check is retained only in scratchpad, outside the delivery.
The import-direction check permits the replacement import.

Change record: coord/changes/K2-scalar-module-cup-upstream-import.md.

## Proved and sorry left

Zero-hole quarantine repair: 0 of 0 local holes closed; 0 holes added;
0 split off. No delivered declaration contains sorry. The existing proof of
AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility
(lem-sc-scalar-cup-module-cup-compatibility) is preserved, including its three
proved private helpers for cycle representatives and class-map surjectivity.

The axiom probe still reports sorryAx through existing dependencies, including
AlgebraicGeometry.Scheme.Modules.scalarCup_positive_resolution_class_compatibility
(new-sc-scalar-cup-positive-resolution-class-compatibility). That dependency is
outside this repair and is unchanged. This delivery restores the assigned
module's public interface; it does not claim to close the full comparison chain.

## No longer needed

The public import of
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations is replaced by its
upstream provider. The old provider is an empty withdrawn module and cannot supply
the public scalar-cohomology names. All three other imports remain necessary for
the statement or proof. No whole module or DAG node is pruned. All node
attachments, dependency edges, the signed statement, and the unit route remain
intact; no node update is needed for this import-only repair.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned zero-hole restoration, not an unfinished theorem body.
The rework row correctly identifies the failure: the archived public import
points to a provider retired during the upstream sync, while the proof imports
bring the actual declarations into scope only privately.

The source-only downstream tool reports zero live importers because the caller
Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison is also quarantined.
Its archive still imports this module and applies the theorem at line 86, and its
node retains the dependency. It is preserved for its own rework; absence from the
live tree is not withdrawal. The caller's signatures and the mathematical meanings
of all targets are unchanged by this provider migration.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
