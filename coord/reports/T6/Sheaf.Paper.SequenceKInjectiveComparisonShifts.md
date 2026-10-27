## What changed

Prove `WeilConjectures.SequenceKInjectiveComparison.sequenceKInjectiveComparisonShifts`
in `Sheaf.Paper.SequenceKInjectiveComparisonShifts`. Use the specified total limit itself as
`RP`, with the composite derived unit, and use the identity for its normalized comparison.
Transport the actual sequence modules to strict varying-ring systems to apply the existing
restricted-tower acyclicity theorem. All arbitrary-replacement, naturality, cocycle and shift
identities are proved by localization, the K-injective Hom bijection, and unit cancellation.

The canonical-unit shift helper is reused from
`Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`. Private proof helpers, including
the general assembly and uniqueness proof, remain
in the item module. The final theorem specializes this complete argument using the proved
coefficient restriction acyclicity clause. No source-library declaration is changed.
The additional public generic constructions
and predicates are attached to the existing comparison node; there are no new results with holes.
The node's proof, dependencies and origin now describe this argument. Explicit types on the
comparison constructions prevent unnecessary unfolding of the localization construction;
see `coord/changes/T6-sequence-comparison-explicit-types.md`. The comparison predicates
now specialize their identical general formulas, and their complete proofs specialize general
localization calculations in the same module. The existing `replacementIso` construction is
preserved verbatim; see `coord/changes/T6-sequence-comparison-generic-predicates.md`.

## Proved and sorry left

Close the one original hole:
`WeilConjectures.SequenceKInjectiveComparison.sequenceKInjectiveComparisonShifts`
(node `lem-pur-sequence-kinjective-comparison-shifts`). No holes are added or split off.
No `sorry` remains in the delivered module.

## No longer needed

Remove the proof imports `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`, and
`Sheaf.CategoryTheory.KInjectiveReplacementTriangulated`. The corresponding proof nodes
`lem-weil-pbc-exact-functor-derived-functor`, `lem-weil-pbc-kinjective-total-derived`, and
`lem-sf-kinjective-replacement-triangulated` are unnecessary for this item: exact localization,
K-injective model computation and coherent shifts are available directly in Mathlib and the
adopted source infrastructure. Remove their obsolete top-level tool-use entries.

The planned `lem-sc-kinjective-quasi-iso-comparison` is also unnecessary here; the proof
uses `CochainComplex.IsKInjective.Qh_map_bijective` directly. No library module is withdrawn.
The ringed-topos composition module remains needed for its proved derivability criterion;
its statement dependency remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan describes a geometric factorization followed by a generic composition
comparison. The actual coefficient restriction already has a sectionwise characterization.
It can be identified with the existing strict-system restriction and use the existing
restricted-tower acyclicity theorem directly. This gives the prescribed normalization
without constructing an extra ringed projection or assuming restriction preserves
K-injectives. The target statement, its hypotheses, and all predicate meanings are preserved.

## Forced adaptations

`Sheaf.Paper.PurSequenceDerivedNormalization` is unclaimed in the current claim record.
Its original proof fails at the last `simpa only` of `composition_model`: the normalization
hypothesis now displays the generic `comparisonIso`, while the expected formula displays
`replacementIso`. The compiler reports a type mismatch between these two definitionally
identical composites and between `lim.mapHomologicalComplex` and `limitComplex`.
Add only `replacementIso`, `comparisonIso`, `restrictionFactors`, `limitComplex`, and `coefficientConstantTowerLimit` to
that `simpa only` list. This unfolds their identical formulas; no statement, visibility,
construction, or other proof line is changed. The original failed against the changed
interface; the adapted module and its transitive consumer are compiled against it.

Validation: the item compiles without warnings in 47.3 seconds;
`PurSequenceComparisonTranspose` and `BasicRealizationShiftSquare` compile unchanged.
The current compiler service reports 75.7 seconds for the latter unchanged module.

`PurSequenceDerivedNormalization` compiles without warnings in 22.3 seconds after the
forced unfolding change. `PurSequenceProjectionHomNormalization` compiles unchanged in
14.1 seconds. Both unchanged consumers were used only for checking and are omitted
from the packet. The delivery contains the item and the one necessary consumer adaptation.
All original theorem signatures and docstrings are preserved. The main theorem's original
hole is closed, with no other hole changed or introduced.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
