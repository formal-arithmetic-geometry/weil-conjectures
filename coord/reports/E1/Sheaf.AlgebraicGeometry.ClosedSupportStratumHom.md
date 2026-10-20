## What changed

Restored lean/Sheaf/AlgebraicGeometry/ClosedSupportStratumHom.lean from its
quarantine archive. In closedSupport_stratum_globalHom, installed the existing
closedSupport_lowerStarExact theorem locally before applying the exact-left-adjoint
criterion for K-injectives. This supplies the newly required PreservesHomology
instance through Mathlib's preservesHomologyOfExact instance.

All archived signatures, definition bodies, docstrings, attributes, and imports
are unchanged. Both attached nodes retain their Lean attachments and all
statement/proof dependencies; their proof step 3 now records the local instance.
Change record: coord/changes/E1-closed-support-stratum-hom-exactness.md.

LeanFinder, Loogle, launcher grep, and direct library searches checked the
exactness/K-injective criterion. The existing adjunction exactness theorem is
the shortest repair; no replacement mathematical construction is needed.

## Proved and sorry left

Zero-hole rework assignment: holes closed 0 of 0; holes added 0; split off 0.
No declaration in the restored module contains sorry. The archived proofs of
stratumDualTensor_preservesFiniteLimits, stratumDualTensor_eq,
stratumDualTensor_derived, and closedSupport_stratum_globalHom are preserved,
with the last proof repaired against the current exactness API.

The original archive's compiler error was reproduced at the K-injective
criterion: failed to synthesize (lowerStar Λ i).PreservesHomology. Installing
the existing finite-colimit-preservation theorem resolves that error. A first
successful compile suggested ordinary let instead of letI; the proof now uses let.

The final module passed compilation and the delivery preflight in dry-run commit
f74c82c9d6 (review class CODEX).

The downstream tool with --allow-missing finds zero live importers. The
quarantined ConstructibleExtContinuityStratum and FormalClosedSupport importers
were inspected; unchanged signatures and definition bodies need no adaptation.

## No longer needed

None. No import, module, declaration, or DAG dependency is removed. Both attached
nodes, their dependencies, and quarantined consumers remain needed and preserved.

## Where the brief, the DAG or earlier work was wrong

This assignment restores an already proved module with zero holes. The sync
changed the exact-left-adjoint criterion to require PreservesHomology explicitly;
the archived proof had not installed its existing exactness theorem locally.
No mathematical statement or unit route was wrong or changed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
