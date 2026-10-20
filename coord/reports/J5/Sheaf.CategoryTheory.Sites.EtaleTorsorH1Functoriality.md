## What changed

Retired Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality in favor of
WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality, as assigned by the
retirement register. Switched the private proof import in the two active consumers,
Sheaf.AlgebraicGeometry.GmPicardPullback and
Sheaf.AlgebraicGeometry.TorsionTorsorDescent. Removed two unused proof imports of route-pivot-dropped modules from
TorsionTorsorDescent. All consumer declarations and proof bodies are verbatim. Updated the existing DAG node's Lean module/file attachment and note.
No source-library file or target statement changes.

The official theorem has the identical complete statement, including both clauses
and universe parameters. A server compile checks an example of the original
statement by applying the official declaration. Its axiom probe reports only
propext, Classical.choice and Quot.sound. Both active consumers are checked alone.
Change record: coord/changes/retire-etale-torsor-h1-functoriality-J5.md.

## Proved and sorry left

Assigned item: zero original direct holes, zero holes closed, zero holes added,
zero split off. The retained official declaration
CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality is fully proved and has
only the three permitted axioms.

One pre-existing direct hole remains untouched in a delivered consumer:
AlgebraicGeometry.Scheme.isIndFiniteEtaleSheaf_of_free_torsion_action in
Sheaf.AlgebraicGeometry.TorsionTorsorDescent (node lem-per-torsion-torsor-descent).
This is a duplicate retirement, not a new proof or decomposition. GmPicardPullback
has no direct holes. No new nodes or statements are introduced.

## No longer needed

Withdraw lean/Sheaf/CategoryTheory/Sites/EtaleTorsorH1Functoriality.lean, listed in
deleted.txt. Both active consumers drop their import of the duplicate and import
the official twin instead. TorsionTorsorDescent also drops the unused proof
imports Sheaf.AlgebraicGeometry.SetLocalSystemCalculus and
Sheaf.DeligneLaumon.TorsionFiniteSubsystem, as required by the route-pivot check.
The duplicate's four public imports and three proof
imports are no longer provided by that file; the official twin supplies its own
existing public interface and complete proof dependencies.

No mathematical nodes or supporting source modules are pruned: the existing node
lem-sc-etale-torsor-h1-functoriality and all its parent dependencies remain and now
refer to the official implementation. The unit route is preserved. All nine DAG
parents were checked, including parents whose Lean files are quarantined.

Three archived consumers (PurityConventions, KummerAdditivity and
ProjectiveBundleFormula) still show the historical import. They remain quarantined
for separate dependency repairs; their exact future import migrations are recorded
in the change record. No archive or mathematical dependency is removed, and their
restoration/compilation is not claimed by this packet.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with sorry or a repair. This assignment
is specifically a depth-zero retirement in coord/retire-items.tsv: the assigned
module already has zero holes and upstream now provides its exact theorem. Writing
a second proof would retain the duplicate. The old node attachment, not its
mathematical statement, required repair.

The old register names seven consumers. Current live sources have only two;
FiniteEtaleEquivalenceH1 and SchemeTorsorPullbackEquivariantHomIsIso already use the
official tree, and the three Paper consumers are quarantined snapshots. None is
silently treated as unused mathematics.

The first server preflight rejected the existing proof imports of
SetLocalSystemCalculus and TorsionFiniteSubsystem in TorsionTorsorDescent because
they are listed in coord/route-pivot-dropped-modules.txt. Neither import supplies
a name in its statement or proof (the proof remains the existing named hole).
Removed both imports and recompiled. No consumer statement or proof is weakened.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
