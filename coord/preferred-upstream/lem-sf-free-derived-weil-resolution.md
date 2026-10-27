## Q26 maintenance: the return's compatibility migration is landed centrally

The return for head `95ce8e89c2f7` correctly required a superset ownership record
and a move of the old exact-derived-adjunction specialization. Its consumer
repair could not pass the worker delivery gate because
`def-sf-open-normalization-data` is outside this item's prerequisite closure.
Maintenance has applied that mechanical migration to `sheaf-dag` directly.

Read the current server source/record before delivering. The canonical module
`Sheaf.CategoryTheory.ExactDerivedAdjunction` now owns both
`CategoryTheory.Adjunction.mapExactDerivedCategory` and the unchanged-signature
`SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`; the latter's
body is `a.mapExactDerivedCategory`. `OpenTensorNormalizationData` publicly
imports the module and no longer declares the specialization. The corresponding
`def-weil-exact-derived-adjunction` record owns both names. This satisfies the
return's module move; do not rebind or redeliver these central library files.

Back up each sandbox file before changing or removing it. Remove these now
redundant files from the active packet (keep backups with a `.bak` suffix):

- `lean/Sheaf/CategoryTheory/ExactDerivedAdjunction.lean`
- `lean/Sheaf/SixFunctors/OpenTensorNormalizationData.lean`
- `dag/nodes/sec-six-functors/def-weil-exact-derived-adjunction.json`
- `dag/nodes/sec-six-functors/def-sf-open-normalization-data.json`

Keep `FreeDerivedWeilResolution.lean` unchanged, the item's actual dependency
on `def-weil-exact-derived-adjunction`, the item record, and the genuine
`def-weil-endofunctor-fixed-pair-category` existing-declaration repair. Refresh
records against current metadata while preserving only their owned changes.
Append a concise maintenance/rebase note to `report.md`. Compile the item and
run the ordinary `deliver2.py --no-push`; fix concrete diagnostics and deliver
through the ordinary wrapper. Do not add the consumer as a fictitious DAG
dependency, rename the existing data module, or change a gate.

See `coord/changes/q26-exact-derived-adjunction-maintenance.md` for the cause and
central migration. No item theorem or proof was supplied by maintenance.
