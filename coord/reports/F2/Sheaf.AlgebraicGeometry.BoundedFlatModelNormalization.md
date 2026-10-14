## What changed

This repair withdraws only `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`
and keeps its four held downstream modules intact. The unchanged public
predicate `AlgebraicGeometry.boundedFlatShiftRepresentative` now lives in the
new module `Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative`. Each held
module changes one forced public import to that replacement; every declaration,
statement, visibility, and proof body in those modules is preserved. The
predicate node's Lean attachment is updated, while the retired normalization
theorem remains detached; the four held paths are retained
in the delivery and therefore are not deleted.

## Proved and sorry left

No new theorem is proved and no `sorry` is added. The four retained modules
remain complete and sorry-free. The retired declaration
`AlgebraicGeometry.exists_bounded_flat_model_normalization`
(`lem-sc-bounded-flat-model-normalization`) is withdrawn, and the predicate
`AlgebraicGeometry.boundedFlatShiftRepresentative`
(`def-sc-bounded-flat-shift-representative`) is retained unchanged in its
replacement module.

## No longer needed

The old import of `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization` is
removed from the four retained modules and replaced by the predicate module.
The retired normalization theorem and its old module are no longer needed by
the active replacement route. The four held telescope modules and their DAG
nodes remain needed as interfaces and are not pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated the four downstream modules as unclaimed and
replaced each entire file with an empty stub. Their recorded holders are G2
(`FlatTelescopeNormalizationIsIso` and
`FlatTelescopeNormalizationUnshiftedIsIso`), E1
(`FlatTelescopeSumComparisonIsIso`), and Y3 (`FlatTelescopeSumModels`), so that
wholesale replacement violated the forced-adaptation rule. This repair keeps
their public interfaces and changes only the dependency line forced by the
withdrawal. The original theorem's DAG statement is unchanged; only its Lean
attachment is retired.

## Forced adaptations

The original held files were compiled against the changed dependency set before
these edits. Each failed solely because `BoundedFlatModelNormalization` was the
withdrawn empty module: the `IsNoetherian Z` binder was reported as `type
expected` in `FlatTelescopeNormalizationIsIso.lean:35:24`,
`FlatTelescopeNormalizationUnshiftedIsIso.lean:139:24`, and
`FlatTelescopeSumComparisonIsIso.lean:60:24`; the bounded predicate use was
reported as `Unknown identifier boundedFlatShiftRepresentative` in
`FlatTelescopeSumModels.lean:402:12`. Replacing that one public import in each
file supplies the same predicate declaration and is the minimal edit; all four
adapted modules compile with their original declarations and proofs.

## Earlier second reading (a previous round; superseded)

The repair preserves all four held theorem declarations and their visibility: the
only edits in each are the forced replacement of the withdrawn public import.
The new predicate module has the unchanged definition and the existing
predicate node now points to it. The assigned normalization theorem is the sole
retired declaration. The exact adaptation details are recorded in
`coord/changes/bounded-flat-model-normalization-withdrawal.md`.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** I compared the delivered files with the
   repository versions. The bounded-flat predicate is byte-for-byte unchanged
   and is attached to its replacement module. The four held modules retain all
   declarations, statements, visibility, and proof bodies; each has only the
   forced public-import replacement. The obsolete normalization theorem is
   intentionally withdrawn and its node attachment is detached.
2. **Proof and compilation checks.** The replacement predicate module and all
   four adapted modules compile with `lcompile.py`; they contain no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. No new theorem
   or hole is introduced. The retained declarations are unchanged and the
   withdrawn theorem is the sole removed declaration.
3. **New statements and search.** No new mathematical statement is added.
   The moved predicate already has the existing DAG definition node, and the
   replacement is exactly that definition rather than a new theorem or a
   restatement. The retired theorem is not reintroduced under another name.
4. **Pruning and imports.** The normalization theorem and its old module are
   unreachable on the active replacement route. The predicate remains needed
   by the four held telescope modules, so it is retained in its own module.
   Their import edits are minimal and the change record documents each forced
   adaptation.
5. **DAG agreement and route.** The predicate node points to the replacement
   declaration, the withdrawn theorem node has no Lean attachment or proof
   dependencies, and the four held nodes retain their existing proof metadata.
   The active telescope route and its realized interfaces are preserved.

The second reading found and corrected the earlier wholesale stubs and the
incorrect adaptation account. The final delivery keeps the held interfaces,
moves the shared predicate, withdraws only the obsolete theorem module, and
records the exact forced import changes.

## Second reading by F2

1. **Statements and interfaces.** I diffed every delivered Lean module against
   the repository version. The four held telescope modules change exactly one
   public import, from `BoundedFlatModelNormalization` to
   `BoundedFlatShiftRepresentative`; their declarations, signatures,
   visibility, and proof bodies are unchanged. The predicate definition is
   byte-for-byte the old definition in its replacement module. The obsolete
   normalization theorem is intentionally withdrawn, and its node is detached
   from Lean.
2. **Proof and compilation checks.** I compiled all five delivered modules
   with `lcompile.py --all`; compilation succeeded without warnings. The
   replacement predicate and retained declarations contain no `sorry`, axiom,
   unsafe, opaque, extern, or implemented-by declarations. The withdrawal
   adds no theorem or hole.
3. **New statements and search.** No new mathematical statement is introduced.
   The moved predicate is the existing definition node, with the same exact
   type and body. The retired theorem is not restated under another name.
4. **Pruning and imports.** The obsolete theorem module is unreachable after
   the replacement route and is listed for withdrawal. The predicate remains
   required by all four held telescope modules. Their import edits are the
   minimal forced adaptations documented in the change record; no active
   telescope node or dependency is pruned.
5. **DAG agreement and route.** The predicate node points to its replacement
   module. The withdrawn theorem node has no Lean attachment, proof, or proof
   dependencies. The four retained nodes preserve their proof metadata and
   the unit route through telescope sum models, comparison, and normalization.

The second reading found no mathematical or interface defect beyond the
earlier wholesale stubs and corrected them by retaining the held files,
moving only the shared predicate, and withdrawing only the obsolete theorem.
