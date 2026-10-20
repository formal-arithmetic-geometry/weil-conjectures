## What changed

Completed the retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf. Listed the duplicate
module in deleted.txt and moved node
lem-sc-section-ring-quotient-chart-overlap-sheaf-map to the already proved theorem
AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_sheaf_map in
WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf.

Adapted the sole consumer, Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap:
its private proof import now uses the upstream twin, and its final application
omits the obsolete e, t, he and hV arguments. Its public signature is unchanged.
No source-library file changes.

Change record: coord/changes/retire-section-ring-quotient-chart-overlap-sheaf.md.
The upstream proof follows the original chart cancellation route and keeps the
unit's route. The upstream theorem is stronger only by dropping unused hypotheses;
it proves the unchanged DAG statement for all its original inputs.

## Proved and sorry left

Zero holes initially in the assigned module; zero holes closed and zero added.
AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_sheaf_map is already proved
in the adopted source library. Its duplicate is retired, rather than counted as a
new proof. No sorry remains in any delivered Lean file; none is split off.
The consumer theorem AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap
still has a complete proof from the same base-map comparison and the source-library
sheaf-map comparison.

Validation: the original assigned module compiled. Changing only the consumer's
import exposed the expected obsolete-argument error at line 93. After adapting
that call, the consumer compiles; delivery checks verify compilation and axioms.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf.
Removed its private proof import from Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap
and replaced it with WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf.
Its private helper fraction_equation_restrict is supplied internally by the
upstream twin. No mathematical proof-dependency node is pruned: denominator
generation, the Proj charts and affine extensionality are still used upstream.
The node is retained and points to the upstream module. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief did not identify this as a retirement; the current
queue and coord/retire-items.tsv do. There is no remaining sorry to prove in the
assigned copy. The adopted source theorem has removed the unused symmetric
nonvanishing parameters e, t, he and hV, so replacing its import alone is
insufficient: the consumer's application also needs the recorded argument update.
The mathematical statement, including empty opens and nonreduced schemes, is
preserved by applying the stronger theorem. No definition repair is needed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
