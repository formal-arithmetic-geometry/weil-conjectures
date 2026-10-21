## What changed

Restored lean/Sheaf/Paper/ConstantToContinuousScalarFlat.lean byte for byte from its
quarantine archive, as required by the assigned coord/rework.tsv row. This repairs a
missing live module after a cluster restore. Its complete existing proof and public
interface are preserved. Change record:
coord/changes/W4-restore-constant-to-continuous-scalar-flat.md.

The theorem constantToContinuous_preservesFiniteLimits constructs the scalar map on
sections, proves continuous functions torsion-free over the PID, lifts finite coefficient
families locally, factors each relation, and transports the resulting flatness to
preservation of finite limits. Its argument covers empty test objects and empty relations.
The existing DAG attachment and dependencies still describe this proof exactly.

Validation: independent compile passed in 11.2 seconds. The theorem axiom probe lists
only propext, Classical.choice and Quot.sound. An overlay compile passed for the item
(13.3 seconds) and the unchanged quarantined FiniteConstantModelResolution consumer
(11.5 seconds). Temporary validation copies and the probe are excluded from delivery.

## Proved and sorry left

This is a restoration repair with zero original holes and zero remaining holes.
AlgebraicGeometry.ProEtale.FiniteConstantModel.constantToContinuous_preservesFiniteLimits
already had a complete archived proof, which is restored and revalidated.
Holes closed: none (0). Holes added: none (0). Split off: none (0).
No declaration uses sorry, directly or transitively, in the checked theorem.

## No longer needed

None. No imports, modules, declarations, nodes or dependencies are removed.
The quarantined parent FiniteConstantModelResolution still uses this theorem, and its
DAG node lem-sfb-finite-constant-model-two-term-free-resolution still cites it.
Loogle, LeanFinder and Mathlib/source searches confirmed the existing component route;
no shorter complete theorem was found. Preserve the archived route and unit route.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with sorry, but the actual assignment is the
listed zero-hole quarantine restoration. The live module was absent; its authoritative
archive contains the complete proof. No mathematical defect, false statement, definition
repair, consumer adaptation or DAG route correction was necessary.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
