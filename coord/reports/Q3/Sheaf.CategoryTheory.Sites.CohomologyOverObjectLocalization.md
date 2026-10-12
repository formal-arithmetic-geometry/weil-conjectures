## What changed

Added an intermediate theorem `cohomology_over_object_localization_addEquiv` and used its additive equivalence to construct the required categorical isomorphism via `AddEquiv.toAddCommGrpIso`.

## Proved and sorry left

The target theorem `cohomology_over_object_localization` is proved. The intermediate theorem `cohomology_over_object_localization_addEquiv` remains sorry and is recorded in node `lem-weil-pbc-cohomology-over-object-localization-addEquiv`.

## No longer needed

No imports or stated proof dependencies were pruned; they remain available for proving the intermediate chain-level comparison.

## Where the brief, the DAG or earlier work was wrong

The existing DAG plan requires a substantial chain-level comparison. No error was found; the upper theorem is reduced to a strictly stronger additive equivalence statement.

## New nodes

`lem-weil-pbc-cohomology-over-object-localization-addEquiv` records the intermediate additive equivalence theorem.

## Earlier second reading (a previous round; superseded)

The additive equivalence statement is strictly stronger than the target isomorphism and the target proof applies it directly. The unit route is preserved through the cited restriction and injective-resolution dependencies.

## Second reading by Q3

1. **Statements unchanged.** Compared the delivered localization module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and the import of the explicitly split-off comparison module changed.
2. **Proof checks.** Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`. The additive-equivalence theorem is the sole remaining named `sorry`, with node `lem-weil-pbc-cohomology-over-object-localization-addEquiv`; no forbidden declarations or hollow definitions occur.
3. **Split-off statement.** Checked the additive-equivalence statement against the target hypotheses and small edge cases (`q = 0`, arbitrary `W`): it is a genuine strengthening needed to obtain the categorical isomorphism, with no extra hypotheses. The node supplies its source, proof plan, and searches, and the declaration is not duplicated in the library.
4. **Pruning and route.** The target proof uses `AddEquiv.toAddCommGrpIso` directly from the split-off theorem. Existing proof-dependency imports remain because they support the planned chain-level comparison; no unused import was identified in the delivered files.
5. **DAG and unit agreement.** The new node's Lean record, theorem statement, proof dependencies, and blueprint link agree. The `sk-prop-cd` unit route remains represented through the restriction and injective-resolution dependencies.

Changed only the target proof/import and added the named intermediate theorem, its node, and this second-reading record.
