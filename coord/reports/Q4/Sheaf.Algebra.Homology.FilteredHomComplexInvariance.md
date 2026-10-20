## What changed

Restored lean/Sheaf/Algebra/Homology/FilteredHomComplexInvariance.lean from the exact
archive named by coord/rework.tsv. Replaced the public Sheaf.CategoryTheory.Filtration
import with WeilConjectures.CategoryTheory.CanonicalFiltration and the public
Sheaf.CategoryTheory.FiniteFiltrationInduction import with
WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension. These are the
upstream providers of the same declarations. All non-import text, all seven public
declarations and every theorem hypothesis and conclusion are unchanged. No archived
file is deleted. See
coord/changes/FilteredHomComplexInvariance-official-filtration-imports.md.

The repaired item compiled on the server in 1.2 seconds with no warnings or errors.
Both official imports also pass tools/import_direction.py may (no cycles).
Read both archived parent modules and their DAG dependencies; neither mentions any
of this module's declarations in a proof or statement, and both remain quarantined
independently. The downstream tool reports zero active Lean importers and zero declaration users;
there are no active consumers to adapt. The node's Lean attachment,
proof steps, proof dependencies and the unit route are preserved without changes.

## Proved and sorry left

Assigned repair completed: the module loads the official filtration API without
constant collisions. Original holes: 1; holes closed: 0; holes added: 0; holes left: 1.
The retained hole is CategoryTheory.filtered_hom_complex_invariance
(lem-trf-filtered-hom-complex-invariance), with its original source and complete
natural-language proof retained verbatim. No split-off statements, new definitions,
axioms or new holes. This delivery claims an import repair, not a proof or decomposition.

## No longer needed

The obsolete import providers Sheaf.CategoryTheory.Filtration and
Sheaf.CategoryTheory.FiniteFiltrationInduction are replaced by their official
upstream counterparts. No mathematical dependency, DAG node or module is pruned.
In particular InjectiveTargetHomSymbol and FilteredComplexSubquotients are retained,
as are both quarantined parents and every original proof dependency.

## Where the brief, the DAG or earlier work was wrong

This is a listed rework repair: the item is absent from lean/ because it was quarantined
after upstream sync, not because its mathematics was withdrawn. The first recorded
IsExhaustive collision also persists through the old finite-filtration import after
the direct filtration import is fixed. Both official replacements are necessary.
The DAG statement and unit route need no correction. Three fresh search modes and
local source searches found no existing proof of the complete filtered invariance
statement; that mathematical proof is not claimed by this API restoration.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
