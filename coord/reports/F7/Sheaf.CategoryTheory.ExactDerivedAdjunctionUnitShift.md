## What changed

Filled the proof of
`CategoryTheory.Adjunction.mapExactDerivedCategory_unit_commShift` in
`Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift`. The statement, docstrings,
visibility, universes and imports are unchanged.

The proof follows the existing five-step DAG argument. The cochain square is
checked in every degree using the canonical identity shift comparisons. The
localized unit is expressed as the image of that cochain unit followed by the
inverses of the two standard exact-derived factorization comparisons, using
`Adjunction.localization_unit_app` for the specified adjunction. These
comparisons, their inverses, the associators and the unitors commute with shifts,
so their composite does too. Finally `Localization.natTrans_ext`, naturality of
the derived unit and cancellation of the localization shift isomorphism give
the square on the entire derived category.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Adjunction.mapExactDerivedCategory_unit_commShift`
(node `lem-pur-exact-adjunction-unit-shift-descent`). Both the cochain and derived
clauses are proved. Zero holes remain; zero holes added; zero split off.
The complete module compiled cleanly through `lcompile.py` in 5.1 seconds.

## No longer needed

None. No imports, modules or declared DAG dependencies were removed. All four
existing proof dependencies are used through their recorded Mathlib interfaces
or the specified exact-derived adjunction definition. No new modules or nodes
are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. Existing proof patterns in
`CondensedOpenAdjunctionLocalization` and `ScalarLocalizationUnitShift` apply
with the independent universes of this item. The
existing DAG route is retained, including the final localization extensionality
step. No target, definition or other module was changed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
