## What changed

Restored Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison from the quarantine
archive identified by coord/rework.tsv. The archive's retired
Scheme.LocallyClosedStratification reference fails compilation; the restored theorem
uses the current Scheme.Stratification while retaining its explicit constructibility
condition. This matches the migration already made to its affine-local predicate.
All four declarations, all imports, and the three canonical construction bodies are
preserved. The only Lean code difference from the archive is that type name.

Updated sk-thm-pe-constructible-comparison's Lean signature and note; its mathematical
statement, proof steps, dependencies, source and unit route are unchanged.
Change record: coord/changes/Q4-restore-constructible-proetale-comparison.md.

The remote compiler accepted the restored module without errors or warnings in 16.5 s.
An importing compatibility check compiled in 6.5 s against the restored item, compiled
first in the same sandbox. It verifies the public constructions and the unchanged
bounded-derived projection used by the archived finite-Tor comparison consumer. The
temporary source was removed before delivery.

## Proved and sorry left

Repair delivery: 0 of 1 existing theorem holes closed; 0 holes split off; 0 new holes
relative to the quarantine archive. The single retained hole is
AlgebraicGeometry.ProEtale.constructibleComparison
(node sk-thm-pe-constructible-comparison). It still has exactly the original named
`:= by sorry` proof, source and complete natural-language proof plan. Restoration
brings that existing hole back to the active library; it is not a new reduction or a
proof of the comparison theorem.

The canonical constructions constructibleComparisonRingMap,
constructibleComparisonPullback and constructibleComparisonComplexPullback contain
no sorry in their own bodies and are restored verbatim. Existing dependency holes are
unchanged. No data are chosen from a new unproved existence theorem.

## No longer needed

None. No imports, declarations, nodes, modules or dependency links are removed.
The quarantine archive remains intact. Zero current importers does not imply this
module is unused: the preserved archived consumers and DAG parents still need it.
No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The active item source is absent because of the recorded cluster-restore quarantine,
not because its mathematics was withdrawn. Its archived first clause uses the retired
Scheme.LocallyClosedStratification name. Scheme.Stratification is the current API and
is already used in the affine-local predicate. Explicit constructibility makes the
two formulations equivalent; no scheme Noetherianity is added. The prior return for Q4
concerns a different item and imposes no repair points on this module.

The full comparison is not already available under the required independent coefficient
and site presentations: LeanFinder returned related condensed-module constructions;
Loogle returned generic categorical equivalences; the recorded Mathlib grep returned
zero matches. The source finite-coefficient comparison additionally assumes a finite
ring and cannot replace this Noetherian-coefficient statement. No proof is claimed here;
this delivery completes the assigned restoration and API repair, which the brief
permits without closing another hole.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
