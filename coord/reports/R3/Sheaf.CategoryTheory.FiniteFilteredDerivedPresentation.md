## What changed

Restored the quarantined `Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation`
and removed its unused public import of
`WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`. All eight definitions,
the structure fields, universes, instance attributes, and mathematical statements
are preserved verbatim. The remaining `FiniteFiltrationInduction` import supplies
the canonical upstream filtration API and the unique induced graded maps actually
used by the presentation. This is an import repair of a zero-hole definition module.

Validation: the original archive compiled, then the repaired module compiled without
warnings (2.6 seconds). A diagnostic run of `#print axioms` on `Complexes`,
`gradedQuasiIso`, `Localization`, `quotient`, `ShiftRepresentative`, `IsConeTriangle`,
`Presentation`, and `Supported` reported exactly `propext`, `Classical.choice`, and
`Quot.sound` for each. The diagnostic commands were removed before delivery.

Consumer check: the live downstream tool lists no importers because the direct consumer
`Sheaf.CategoryTheory.FilteredFunctorGradedComparison` is quarantined. Read its complete
preserved source and checked that it uses none of the removed subquotient API. Its
original compile stops at an unavailable `FiniteFilteredLocalization.olean` through
its independent proof import `FilteredTruncationTriangle`. A sandbox-only interface
probe, retaining every consumer declaration and proof but omitting that proof import,
compiled cleanly against the repaired presentation. The probe is not delivered and
no consumer is adapted. Full restoration of that consumer still needs its other
quarantined dependency.

Change record: `coord/changes/R3-finite-filtered-derived-presentation-import.md`.
The existing DAG attachment, all dependency edges, and the unit route are preserved.

## Proved and sorry left

Zero original holes; zero closed; zero added; zero split off; zero remaining holes.
This delivery repairs imports and restores the definitions, and claims no new proof.
No `sorry` appears in the delivered module or any new module.

## No longer needed

Removed the direct public import of
`WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`: the presentation uses
filtration steps and graded quotients from the canonical filtration interface, but
none of that module's `complexStep`, `complexQuotient`, cycle, or boundary definitions.
The upstream module and all its declarations stay in the library. No DAG node or
module is withdrawn, and no statement dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The listed quarantine error came from importing both the former Sheaf filtration
implementation and the adopted canonical upstream filtration implementation. The
current `FiniteFiltrationInduction` source already imports only the canonical API,
so the preserved archive now compiles. This packet additionally removes the unused
subquotient import rather than delivering a byte-for-byte restoration alone.
No mathematical statement or definition defect was found. The module contains zero
holes, as allowed for an assigned rework repair. Its concrete localization, cone
normalization, and pure comparison normalization are preserved, including zero
complexes and empty support intervals.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
