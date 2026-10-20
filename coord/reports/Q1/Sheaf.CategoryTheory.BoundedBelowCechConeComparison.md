## What changed

Restored Sheaf.CategoryTheory.BoundedBelowCechConeComparison from its recorded
quarantine source. Replaced public Sheaf.CategoryTheory.DoubleComplexTotal with
public Mathlib.Algebra.Homology.TotalComplex and Mathlib.Data.Int.Interval.
This fixes the recorded collision between the old Sheaf filtration API and
WeilConjectures.CategoryTheory.CanonicalFiltration, without changing any
construction, statement or proof. The repaired module compiles remotely in 1.7 s.
Change record: coord/changes/bounded-below-cech-cone-import-repair.md.

## Proved and sorry left

This is a quarantine import repair, not a proof or decomposition.
Holes closed: 0. Holes added: 0. Holes retained: 1, namely
HomologicalComplex₂.boundedBelow_cech_cone_comparison
(lem-trf-bounded-below-cech-cone-comparison).
Both cechTotalMapCone and cechTotalMapConeStep retain their real constructions.
All declarations and docstrings after the imports are byte-identical to the archive.

## No longer needed

Removed the broad public import Sheaf.CategoryTheory.DoubleComplexTotal from this
module. The definitions use only Mathlib's total-complex constructions and integer
intervals, now imported directly. No node or module is withdrawn or declared
mathematically unnecessary: def-sp-double-complex-total, all original proof
dependencies, the two quarantined parent modules and the unit route stay intact.
The theorem's existing proof-only imports are retained for its unchanged plan.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it is quarantined, not because it is unused.
Its exact archived failure was reproduced with lcompile.py. The current source of
DoubleComplexTotal has migrated to CanonicalFiltration, but the published compiled
artifact still brings in the old Sheaf filtration declaration. Importing only the
Mathlib constructions actually used by this file avoids that collision and makes
the integer interval instance an explicit dependency.
The natural-language theorem and its Lean attachment require no correction.
The registered first-quadrant spectral-sequence theorem is currently an E2 natural-
index interface; proving the stronger integer-index E1/convergence statement here
is separate from this assigned quarantine repair. No theorem is claimed proved.
The source-only downstream command cannot enumerate an absent quarantined module;
manual searches of both source trees found zero live consumers and exactly the
two archived direct importers recorded in the change record. Their private imports
and unfinished proofs require no source adaptation for this import-only repair.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
