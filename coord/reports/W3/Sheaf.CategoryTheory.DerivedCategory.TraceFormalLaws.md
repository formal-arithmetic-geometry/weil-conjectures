## What changed

Restored `lean/Sheaf/CategoryTheory/DerivedCategory/TraceFormalLaws.lean` from
its exact quarantine archive, preserving every declaration signature, visibility,
attribute and import. Repaired `DerivedCategory.traceExtendScalarsAdditive` by
using `(ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive` instead of
the removed `ModuleCat.extendScalars_additive_sheaf` declaration.

Proved `DerivedCategory.perfectCategoricalTrace_conjugacy`: install the canonical
braiding and the two canonical right duals, unfold the two trace wrappers, apply
`CategoryTheory.MonoidalCategory.trace_eq_of_iso` to `hw.symm`, and apply
`perfectTraceScalar` to its equality. This uses the adopted source library's
complete categorical conjugacy proof, with no chain-supertrace dependency.
Updated step 2 and the proof-origin description of
`prop-trf-trace-formal-laws` accordingly; the remaining steps are unchanged plans.

The restored and repaired item compiles cleanly through lcompile.py in 2.6 s.
No new helper modules, dependencies, statements, axioms or split-off lemmas were added.
The change record is `coord/changes/trace-extend-scalars-additive-restoration.md`.

Searches: LeanFinder for categorical trace invariance returned ordinary linear
trace results; Loogle `"trace", "iso"` returned no results. The launcher grep
query returned no matches. Direct source searches found the exact general
categorical theorem in
`WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/Braided.lean` and the
adjunction-based additivity proof already used throughout the current library.

## Proved and sorry left

Closed 1 of the archive's 6 theorem holes:
`DerivedCategory.perfectCategoricalTrace_conjugacy`.
The additivity instance's missing-identifier repair is also complete and has no
hole. Relative to the quarantine archive, added 0 holes; split off 0 statements.
The live `lean/` path is absent, so restoration reintroduces the five archived
theorem holes listed below; none is a newly introduced statement.

Five existing theorem holes remain, all on `prop-trf-trace-formal-laws`, with
unchanged statements and complete original proof docstrings:

- `DerivedCategory.perfectCategoricalTrace_filtered_additivity`
- `DerivedCategory.perfectCategoricalTrace_triangle_counterexample`
- `DerivedCategory.perfectCategoricalTrace_scalar_extension`
- `DerivedCategory.perfectCategoricalTrace_cohomology`
- `DerivedCategory.perfectCategoricalTrace_common_stage`

This is the listed quarantine repair, together with the completed conjugacy
clause; the five pre-existing holes have not been moved or decomposed.

## No longer needed

Clause (1) no longer uses `lem-trf-chain-supertrace` or a bounded chain model.
Removed that citation from step 2. This does not prune its module or the node
from the whole item: other retained clauses still need it. No import or module
is withdrawn. The original proof-dependency imports and node attachments are
preserved for the remaining clauses, as required for quarantine restoration.

## Where the brief, the DAG or earlier work was wrong

The archived additivity instance refers to a declaration removed by the upstream
sync. Its replacement follows immediately from the current scalar-extension
adjunction. No mathematical statement correction is needed. The detailed
chain-model argument originally planned for conjugacy is already supplied more
generally by the source library's categorical trace theorem; its proof is the
same right-duality cancellation required by the unit route.

The downstream script cannot enumerate a quarantined module; the change record
therefore records the explicit source search, including all three quarantined
consumers. No consumer's original interface changes.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
