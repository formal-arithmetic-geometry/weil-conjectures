## What changed

Proved `WeilConjectures.SemilinearSections.semilinearScalarData` without changing its
statement. Added a proof-only import of `Sheaf.CategoryTheory.SystemScalarModel`.
A proved private helper converts its existing normalized ordinary and derived
adjunctions to `ScalarData`, then applies the conversion to the sequence-site ring
map and every level map. The ordinary unit proof cancels the object-identification
maps and uses `one_smul`; the derived transpose proof cancels the localization
comparison isomorphism. This conversion already occurs as a proved private helper
in `Sheaf.Paper.SemilinearSystemsExistence`; no import of that larger module is needed.

Validation: the assigned module compiled cleanly through `lcompile.py` in 6.1 seconds.

Updated the existing node's proof, proof dependencies and proof origin accordingly.
`lem-pur-system-scalar-model` is used as a generic tool for exactly the existing
change-of-rings step, preserving the unit route. Its complete Lean proof was read.
No target statement, definition, public import or consumer changes.

## Proved and sorry left

Closed 1 of 1 existing holes:
`WeilConjectures.SemilinearSections.semilinearScalarData`
(node `lem-coef-semilinear-scalar-data`).

Added 0 holes; 0 holes remain in the item. No split-off statements.

## No longer needed

No imports or modules withdrawn. The public import of
`Sheaf.Paper.SemilinearDerivedCalculus` is retained. Its node
`def-coef-semilinear-derived-calculus` is no longer a proof dependency: the proof
needs the `ScalarData` and sequence-site definitions in
`def-coef-semilinear-system-models`, together with the existing normalized generic
scalar-model theorem. It remains a statement dependency, and this delivery makes
no claim that the module is globally unused. No additional construction or split
of ordinary scalar extension, derived scalar extension or adjunction normalization
is required for this item.

## Where the brief, the DAG or earlier work was wrong

The old proof step cited only interface definitions while asking to construct
normalized scalar data. The required normalized scalar-model theorem already exists
as `SheafOfModules.nonempty_systemScalarModel`, and a complete conversion to this
exact interface already appears privately in `SemilinearSystemsExistence`.
The new dependency records this existing theorem explicitly. Searches through the
required search wrapper found generic Mathlib adjunctions but no exact Mathlib
match; direct repository search found and checked the existing conversion.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
