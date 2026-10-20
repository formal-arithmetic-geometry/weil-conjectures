## What changed

Repaired the current quarantine assignment for
`Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare`, restoring the archived
module with its original theorem, statement, docstring, dependencies and hole.
The listed failure was a duplicate declaration collision between the Sheaf and
upstream implementations of the module/abelian common-resolution comparison.

Changed the canonical comparison and its two proof-support modules to import the
adopted upstream extension, and selected that extension in the restored item too.
Made the item's ModuleCohomologyFMap import public because its theorem statement
uses that name. The first repaired compile exposed this visibility error explicitly.
No declaration signature, definition body, proof body or target statement changed.
Updated the resolution-naturality node's Lean attachment to the upstream extension,
which reexports the original theorem and supplies the two cached instances and helper.
The old Sheaf module and all upstream declarations remain in the repository.

Validation: the remote compiler accepted both proof-support modules and the canonical
comparison together. It then accepted the restored item with those sandbox artifacts.
The import-direction check accepts the upstream dependency. The consumer audit reads
both the active tree and all archived quarantined consumers.

Change record: `coord/changes/J2-normalized-pullback-resolution-imports.md`.

## Proved and sorry left

This is an import/build repair, not a mathematical proof or decomposition.
Item holes closed: zero of one. Holes added: zero. Split off: zero.

The unchanged original hole is
`AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square`
(node `lem-weil-pbc-qcoherent-normalized-pullback-square`). Its Cech-refinement proof
plan and all recorded mathematical dependencies are preserved.

The adapted support module CoherentEtaleComparisonMorphismExists also retains its
pre-existing hole `AlgebraicGeometry.Scheme.Modules.CoherentEtale.exists_normalized_map`
(node `lem-pbc-coherent-etale-normalized-additive-map`); this packet adds no hole there.
The other two adapted modules have no local sorry.

## No longer needed

Removed the import of the duplicate
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` from the item,
CanonicalCoherentEtaleComparison, CoherentEtaleComparisonMorphismExists and
CoherentEtaleEffacingSequence. Replaced it by the adopted upstream extension;
the mathematical resolution-naturality dependency remains needed. No mathematical
node, declaration, unit route or module is withdrawn. No proof-plan import is pruned.

## Where the brief, the DAG or earlier work was wrong

The rework archive correctly preserved the mathematical obligation. The scheduled
upstream sync left its canonical-comparison dependency importing a duplicate local
implementation, while resolution normalization already imported the upstream copy.
Those implementations cannot be loaded together. The resolution-naturality node
still pointed to the duplicate implementation, so merely changing the item's own
import would not fix the transitive collision or future import regeneration.

The archived item also privately imported a declaration used in its public statement.
Both errors are now repaired without deleting the archive or weakening the theorem.
The broader mathematical theorem is still open; no claim of a net hole reduction is made.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
