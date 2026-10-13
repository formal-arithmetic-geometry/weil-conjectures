## What changed
Split the parent proof into two imported component theorems and combined them in
`grothendieckDerived_compact_localization_model`. The component theorems are explicit
public statements with documented proof plans and are the remaining work items.

## Proved and sorry left
The parent theorem is proved by destructing the compact source component and applying
the exact localization component. Sorries remain in
`grothendieckDerived_compact_source` and `grothendieckDerived_exact_localization`,
with nodes `lem-g2-grothendieck-derived-compact-source` and
`lem-g2-grothendieck-derived-exact-localization`.

## No longer needed
None; all original public imports remain needed for the component interfaces.

## Where the brief, the DAG or earlier work was wrong
The original node treated compact generation and exact localization as one monolithic
sorry. They are independent strictly smaller statements and must be tracked separately.

## New nodes
`lem-g2-grothendieck-derived-compact-source` and
`lem-g2-grothendieck-derived-exact-localization`.

## Second reading by X2

1. Compared the delivered parent module with the repository version. The target
   declaration's signature is byte-for-byte unchanged; only proof-only imports and
   the proof body were added. The two component declarations are new, documented
   split statements and do not alter an existing interface.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile
   successfully; the only remaining `sorry`s are the two named component theorems,
   and no `sorry` occurs in a definition. No forbidden `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by` declaration was introduced. The parent theorem's
   dependency on `sorryAx` is exactly through those explicitly split statements.
3. Searched the repository and sandbox for all three declaration names and found no
   pre-existing duplicate. The component conclusions are the strict compact-source
   and exact-localization factors of the parent conclusion, with the same hypotheses
   and universe parameters, so they are true and exactly the reductions required by
   the parent proof.
4. The proof follows the shortest available route at this layer: destruct the
   compact-source package, install its structures, apply the exact-localization
   package, and reassemble the parent existential. Both split statements retain the
   unit route; no old proof dependency or import became unnecessary.
5. Checked the two new DAG nodes against their Lean declarations and the parent
   proof. Their `proof_deps`, `proof_origin`, `lean` records, chapter, and unit agree
   with the delivered files; the parent uses both declarations exactly once.

Changed files are the parent proof module, the two component theorem modules, their
 two split DAG nodes, and this report. No imports were pruned and no additional holes
 were introduced beyond the two documented component holes.
