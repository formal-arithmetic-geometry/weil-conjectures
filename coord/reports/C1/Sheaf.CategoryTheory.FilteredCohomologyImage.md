## What changed

Replaced the duplicate `cohomologyImage` construction by an abbreviation of the existing
`homologyFiltration`. The module now publicly imports the adopted upstream
`WeilConjectures.CategoryTheory.FilteredCohomologyImage`, which supplies the already proved
`cohomologyImage_isFinite`. Removed the duplicate theorem and its private
`complexStep_antitone` helper. Updated the finiteness node's Lean attachment to the upstream
theorem; all mathematical statements, proof dependencies, parents and unit steps remain.

Kept the compatibility module because current consumers use its public name. Adapted one
proof step in the newly available, unclaimed `Sheaf.CategoryTheory.FilteredPageTwoComparison`.
All public signatures remain unchanged. The change record is
`coord/changes/cohomology-image-canonical-abbreviation-C1.md`.

## Proved and sorry left

Zero-hole definition repair: proved 0 of 0 sorries; added 0; split off 0; left 0.
The complete upstream proof of
`CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite` is reused.
This is canonicalization of an existing definition and removal of a duplicate proof,
not a newly proved mathematical result or a decomposition.

The compiled equality probe proves by `rfl` that the original full construction equals
`homologyFiltration`, and that the new abbreviation equals the original construction.
It also applies finiteness at the old `cohomologyImage` conclusion without any conversion.
The five direct consumers and the two immediate paper callers are checked verbatim.
The axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The duplicate construction body, the duplicate finiteness proof and its private
`complexStep_antitone` helper are removed. The item's direct imports of
`WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`,
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, and
`Mathlib.Algebra.Homology.QuasiIso` are replaced by the canonical upstream import.
The upstream module supplies the necessary public API.

No module or mathematical node is pruned. This module remains a required compatibility
interface for the original `cohomologyImage` name; all consumers and quarantined parents
can continue to use it. No new node is introduced.

## Where the brief, the DAG or earlier work was wrong

The current item has no sorry: it is a duplicate repair listed in `coord/retire-items.tsv`.
The earlier reviewed T1 full withdrawal was removed during batch recovery. Repeating that
withdrawal now changes signatures in modules held by C4 and J1. Preflight rejected the
attempt for `cycle_class_image`, `cohomologyImage_cycle_map`, and
`filtered_class_preimage`. This revised packet preserves those consumer signatures by
retaining an abbreviation, as the project's one-definition rule permits.

The actual construction and complete finiteness theorem are supplied by the adopted
upstream module. The compatibility abbreviation contains no new data or choice: its body
is precisely the existing `homologyFiltration`. The five original direct consumer sources are left intact,
and the quarantined parent and its mathematical dependencies are preserved.

The returned head `e17a2ae819` was refused because the archived consumer
`Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence` appeared only in prose,
not in the change record's `## Users` table. Added its explicit row, checked its image-map
helper, abutment filtration and finiteness call, and retained its archive and node unchanged.
Also corrected the earlier record's obsolete description of
`Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`: it has been restored and no
longer uses this module. The current downstream scan is covered by the existing table.

The refreshed preflight also found the newly available consumer
`Sheaf.CategoryTheory.FilteredPageTwoComparison`. Added its `## Users` row after
checking its stationary graded-piece comparisons, filtered homology maps and finiteness
calls. Its original fails to rewrite through the abbreviation, so one proof step is
adapted as described below; all public signatures are unchanged.

## Forced adaptations

`Sheaf.CategoryTheory.FilteredPageTwoComparison` (unclaimed) landed while this repair
was being prepared. Its unchanged original was compiled against the repaired item and
failed at line 244 in `cohomology_restriction_naturality`:
`Tactic rewrite failed: Did not find an occurrence of the pattern
factorThruImageSubobject ?f ≫ (imageSubobject ?f).arrow`.
The old `dsimp only [DecreasingFiltration.cohomologyImage, DecreasingFiltration.step]`
left a `homologyFiltration` projection where the rewrite expected `imageSubobject`.
Replaced only original line 243 by an explicit `change` to that definitionally equal
image-subobject expression (adapted lines 243--249). The original rewrites then succeed.
The adapted file compiles; it has zero holes and introduces no declarations, signatures,
imports, attributes or visibility changes.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
