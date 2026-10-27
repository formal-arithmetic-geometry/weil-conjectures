# Q26 exact-derived-adjunction compatibility migration

Maintenance of returned delivery `lem-sf-free-derived-weil-resolution`, head
`95ce8e89c2f7`, dispatcher key `lem-sf-free-derived-weil-resolution@95ce8e89c`.

The return requires moving the original common-universe
`SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` into
`Sheaf.CategoryTheory.ExactDerivedAdjunction`, preserving its signature, defining
it by `a.mapExactDerivedCategory`, and retaining both names in the owning
definition node. `OpenTensorNormalizationData` publicly imports that module.

The saved worker packet implements the migration, but `stage2_delivery.read`
excludes `def-sf-open-normalization-data`: it is a consumer of the dependency,
not a prerequisite of this item. Its module subsequently has no recognized
owner, so preflight rejects the consumer compatibility repair. Adding the
consumer as an artificial prerequisite would misrepresent the mathematics.

Maintenance therefore applies this already-requested mechanical migration
centrally. The item's theorem statements and proofs are left to the normal
delivery/review path. The definition record keeps its original primary
declaration and statement, and owns both declarations as a superset. The old
specialization's docstring is preserved along with its complete signature.
No mathematical statement, DAG edge, or existing theorem proof changes.

Backups of the two existing files are adjacent `.maint-Q26-1792788379.bak`
files; the new module has an absence marker with the same suffix. Backups are
not staged. Individual validation uses `tools/lean_file.sh` with
`SHEAF_GROUP=maint-Q26-1792788379` and `SHEAF_FILE_TIMEOUT=60`.

The next worker must keep the landed dependency unchanged, remove the redundant
dependency/consumer module and record copies from its packet, retain
`FreeDerivedWeilResolution.lean` and the genuine fixed-pair binding repair, and
run `deliver2.py --no-push` followed by the ordinary delivery. The return's
module move is satisfied by this maintenance commit.

Validation completed before commit (60 s each, sequential):

- `Sheaf.CategoryTheory.ExactDerivedAdjunction`: 2.1 s.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`: 50.6 s on retry; the first
  invocation reached the existing 60 s timeout. Saved worker evidence also
  records an unchanged-source baseline timeout. The limit remains 60 s.
- `Sheaf.SixFunctors.OpenTensorNormalization`: 36.8 s.
- `Sheaf.SixFunctors.ClopenCompositeCounitNormalization`: 7.8 s.
- `Sheaf.SixFunctors.RoosAdjunctionUnitCoherence`: 17.5 s.

All successful invocations returned zero without diagnostics. No global build
was run and no shared published build artifact was modified.
