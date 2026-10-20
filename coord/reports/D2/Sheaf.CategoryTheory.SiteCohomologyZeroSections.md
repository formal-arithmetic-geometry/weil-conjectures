## What changed

Withdraw `Sheaf.CategoryTheory.SiteCohomologyZeroSections`, listed as a duplicate in
`coord/retire-items.tsv`. The original module already compiled and contained zero
holes. Its evaluation is the existing upstream `Sheaf.objectCohomologyEval₀`, and its
three properties are `CategoryTheory.siteCohomology_zero_section_properties`.
Adapt the sole direct consumer, `Sheaf.CategoryTheory.CohomologyColimitSitesZeroComparison`,
by replacing its proof import, updating the theorem name and swapping the evaluation's
object/sheaf arguments. All consumer signatures and public imports remain identical.
Attach `lem-weil-pbc-object-cohomology-zero-evaluation` to the existing proved upstream
theorem; no mathematical statement or proof dependency changes.
Change record: `coord/changes/retire-site-cohomology-zero-sections.md`.
The consumer uses declaration-scoped `backward.isDefEq.respectTransparency true` and
`backward.defeqAttrib.useBackward true` to keep the unchanged pullback/Ext statement's
elaboration within the single-file limit (25 seconds in the final individual check).
The first dry run passed, but a subsequent push check timed out; diagnostic compilation
identified the statement's pullback/Ext compatibility hypothesis, and the scoped options
resolved the later timeouts. No compilation limit was raised.

## Proved and sorry left

Holes before: zero. Holes closed: zero. Holes added: zero. Split off: zero.
No sorry remains in either delivered module. This is duplicate retirement, not a
new proof or decomposition. The adopted theorem `CategoryTheory.siteCohomology_zero_section_properties`
and its evaluation API were already proved. The adapted theorem
`CategoryTheory.cohomology_colimit_sites_zero_comparison_injective` retains its complete
proof and exact statement.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.SiteCohomologyZeroSections` and its private import
from `Sheaf.CategoryTheory.CohomologyColimitSitesZeroComparison`. The duplicate definition
`CategoryTheory.siteCohomology_zero_section` and theorem
`CategoryTheory.siteCohomology_zero_section_properties_sheaf` are retired in favor of the
existing upstream declarations. The object-evaluation DAG node remains needed and now
points upstream. No other node or module is pruned. The unit route and the source
library's declarations, signatures, attributes and imports are preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

This assignment has zero holes rather than an unfinished proof. The retirement
inventory correctly identifies the missing name migration in its only direct consumer.
The node's Lean attachment still named the duplicate despite its audit recording the
proved upstream theorem. The two evaluation definitions have identical formulas; the
upstream version takes object then sheaf, and synthesizes canonical sheafification.
The consumer already uses this canonical instance, so its normalization equations and
zero-detection argument are preserved. No false statement was found and no new node
was needed. Searches through msearch (LeanFinder, Loogle and grep), the local Mathlib
and both library roots confirmed the existing Ext-Hom and upstream evaluation API.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
