## What changed

Restored lean/Sheaf/AlgebraicGeometry/EtaleAffineLineShriekSheafConstructible.lean
from the quarantine path named in coord/rework.tsv. Replaced the retired private
Sheaf comparison import by its canonical WeilConjectures source import, and
migrated all eight comparison applications to
Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf. The unchanged
archive failed compilation with unknown comparison constants; the repaired file
compiles in 7.6 seconds. Public imports, all signatures, docstrings, and the existing
limit-descent/closed-induction/base-change proof are preserved.

Change record: coord/changes/K7-restore-affine-line-shriek-constructible.md.
No live downstream consumers exist; the archived parent
Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility uses the identical
restored signature and requires no adaptation. The node attachment, dependencies,
and unit route are preserved unchanged.

## Proved and sorry left

This is an assigned zero-hole restoration/API repair: 0 holes closed, 0 holes added,
0 holes remaining, and 0 split off. The restored public theorem
AlgebraicGeometry.isConstructibleEtaleModuleSheaf_affineLine_shriek and all four
existing private helpers compile with complete proof bodies. No sorry declaration
is left in the item or added elsewhere. The proof continues to use the existing
named library dependencies; this restoration makes no new claim about their axioms.

## No longer needed

Removed the retired private import
Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison, replacing it with
WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison. No
mathematical dependency, node, or other module is pruned: the comparison node
remains needed and already points to the canonical source theorem. No unused
proof route was introduced. Searches of WeilConjectures and Sheaf, and the three
msearch modes, found no shorter replacement for the existing complete argument.

## Where the brief, the DAG or earlier work was wrong

The item is currently absent from lean/ because it was quarantined after a global
build failure. Its archived proof is already complete, with zero sorry. The stale
comparison import/name in that archive predates the retirement documented by D9;
restoring it without the API migration fails compilation. The current node already
records the canonical comparison dependency correctly and needs no modification.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
