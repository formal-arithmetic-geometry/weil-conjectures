## What changed

Restored `lean/Sheaf/Paper/IntegralConstructibleCompactness.lean` from the quarantine path
recorded in coord/rework.tsv. Replaced its public import of the withdrawn
`Sheaf.CategoryTheory.CompactObject` with the canonical
`WeilConjectures.CategoryTheory.CompactObject`. Every declaration, definition, signature,
proof, and other import is byte-for-byte identical to the archive. The repaired item
compiles on the project server in 5.2 seconds without errors or warnings.

Change record: `coord/changes/X7-integral-compactness-canonical-import.md`.
A fresh importing consumer compiled together with the restored item (10.0 and 4.1
seconds). It successfully checks the canonical `CategoryTheory.IsCompactObject`, the
assertion definition and the original theorem through the restored public interface.
`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` and inherited `sorryAx`:
the module has no local holes, but it still depends on unfinished imported results. This
repair does not claim to close those dependencies.

The two original direct archived consumers were attempted against the restored module.
`IntegralProperDirectSums` cannot load its unrelated unpublished/quarantined dependency
`Sheaf.Paper.IntegralProperCohomologicalBounds` (missing object file), before elaborating
any declaration. No consumer source adaptation is required by this import replacement.
`BrownHypothesesGeneration`'s first check received no answer from the busy compile server;
no successful whole-file compile is claimed for it. The focused importing consumer above
verifies the restored public interface directly.

## Proved and sorry left

Assigned repair completed, with 0 original sorries and 0 remaining sorries.
Holes closed: none. Holes added: none. No split-off declarations.
`AlgebraicGeometry.ProEtale.integralConstructibleCompactness` retains its complete archived
proof from the existing integral Ind realization, lower-tail vanishing, finite-window
comparison, and localizing-closure theorem. Its matching node remains
`det-prop-int-compactness-compact` with its existing Lean attachment and dependencies.
`AlgebraicGeometry.ProEtale.IntegralConstructibleCompactnessAssertions` retains its genuine
explicit definition, with no postponed data. This is a restoration/import repair, not new
proof progress.

## No longer needed

Removed import: `Sheaf.CategoryTheory.CompactObject`, already withdrawn to an empty module.
It is replaced by the identical canonical upstream notion. No mathematical dependency,
DAG node, module, or proof step is pruned. No deletion requested.

## Where the brief, the DAG or earlier work was wrong

This item is a quarantined repair with zero local holes, rather than an unfinished theorem.
The archive still publicly imported an empty retired compatibility module. As a result its
public assertion definition could see `CategoryTheory.IsCompactObject` only through a
private proof import, which Lean's module visibility correctly rejects. The actual compiler
error was reproduced before changing the import. The public canonical import repairs this
without altering any mathematics or the existing DAG route.

LeanFinder returned generic derived t-structure results, and Loogle did not index the
project-specific `IsCompactObject` name. Direct source search located the exact canonical
upstream definition and the already-used thick compact objects theorem. No shorter
mathematical route is required for this one-line restoration repair. The old quarantine
archive remains untouched.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
