## What changed

Retired Sheaf.CategoryTheory.CompactObject in favor of the official twin
WeilConjectures.CategoryTheory.CompactObject, following the retirement hand-off.
The old re-export packet is superseded: the copy is absent from sandbox sources and listed
in deleted.txt. All five current consumers now publicly import the twin directly:

- Sheaf.CategoryTheory.DerivedModuleRankOneCompactInjective
- Sheaf.CategoryTheory.DerivedModuleRankOneCompactSurjective
- Sheaf.CategoryTheory.DerivedModuleRankOneCompact
- Sheaf.CategoryTheory.DerivedModuleRankOneProperties
- Sheaf.Paper.PurEtaleLisseStratumCompact

The sole DAG attachment, def-pc-compact-object, points at the upstream module and file.
CategoryTheory.IsCompactObject has the identical fully qualified name, universe parameters,
hypotheses and definition body. No consumer declaration, statement or proof changes. No
upstream source or target is edited; the existing unit route stays intact.

Change record: coord/changes/K9-compact-object-canonical-reexport.md.
Validation: all five adapted consumers compile in dependency order using lcompile.py.
The complete retirement packet passed deliver3.py --no-push with review class CODEX.
The appended axiom probe passed for the four rank-one modules; for
PurEtaleLisseStratumCompact it timed out after 60 seconds, while the ordinary consumer
compilation succeeded. The delivery tool explicitly accepts this probe limitation and
records that the merge runs it again. Every consumer proof is unchanged.
An import-graph scan confirms the five direct consumers are also all transitive consumers.

## Proved and sorry left

Retirement of a zero-hole definition module: proved 0 of 0 sorries; 0 added; 0 split off.
No sorry remains in the retired item. All existing consumer proofs are retained verbatim,
and no new holes are introduced. This is duplicate pruning, not a mathematical proof gain.

## No longer needed

Withdrawn module: Sheaf.CategoryTheory.CompactObject.
Removed its public import from every current consumer, replacing it with the twin's public
import. The duplicate CategoryTheory.IsCompactObject definition is unnecessary; the
canonical definition remains in WeilConjectures.CategoryTheory.CompactObject. No DAG node
or upstream declaration is deleted, and no additional proof dependency is pruned.
A scan of all current Lean sources after applying the packet finds no reference to the copy.

## Where the brief, the DAG or earlier work was wrong

The previous packet retained a re-export shim and was refused as a zero-hole no-op repair.
The current RETIRE instruction requires full withdrawal and direct consumer adaptation;
this packet does that. The required initial dry run reproduced the prior gate diagnostic
before those changes were made. The hand-off inventory lists 36 historical consumers, but
only the five listed above still reference the copy in the current source tree. The DAG's
mathematical statement was already correct; only its Lean attachment needed redirection.
No proof fallback or hollow definition is needed.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
