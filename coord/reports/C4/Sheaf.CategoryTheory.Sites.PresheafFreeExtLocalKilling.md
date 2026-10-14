## What changed

Verified the repair requested by upstream review #1428 against the current repository
and normalized its direct vanishing equation to the same `= 0` notation as
its sole caller. Lean infers exactly the previously annotated Ext type. The conclusion of
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` contains the
vanishing equation directly, without `∃ h : … = 0, True`. Its sole caller,
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`, applies that conclusion
directly. The existing change record is
`coord/changes/presheaf-ext-local-killing-witness-padding.md`; it records the
already landed repair and subsequent explicit typing of zero. The elaborated statement is unchanged. Updated the witness node
`lean.statement` to match the normalized source. The new change record is
`coord/changes/presheaf-ext-local-killing-zero-normalization.md`.
No definition, import, or caller change is needed.

## Proved and sorry left

Both `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and
`CategoryTheory.Sheaf.exists_presheaf_ext_local_killing` are already proved.
The private helpers `epi_locally_surjective` and `exists_presheaf_cover_lift`
are also proved. Holes closed in this delivery: none (0 of 0).
Holes added: none. Sorries left in the module: none.

The witness proof constructs the small presheaf of generator/lift pairs,
proves its projection locally surjective, and combines its free-sheaf lift
with `Ext.exists_epi_comp_eq_zero`. The last theorem uses the witness directly.
The DAG records these same steps and the unpadded signatures.

## No longer needed

None. No imports, nodes, or modules are removed. The proof continues to use
`Sheaf.CategoryTheory.Abelian.ExtEpiEffacement`; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The repair queue entry is stale: padding was already removed in landing
`20261013T190156-L-3221515`, as recorded by the existing landed change record.
The current DAG witness node also records that statement correction. Both
proofs were subsequently verified by landing `20261014T043249-L-1304302`.
A source search and the downstream-use check find no other caller of the
witness theorem, so no forced adaptations are required. The previous worker's
reported delivery-tool blockers have been corrected in the current script:
listed repairs need not close a sorry, and a worker dry run permits the
second-reader section to be supplied later by the independent reader.

The first dry run confirmed that preflight still requires a changed Lean module
even for an already landed repair; the source normalization supplies that change
without altering the proposition.

## Second reading by C4

1. Compared the delivered Lean module with the repository version. The only
   declaration change is the normalization of the witness equation from an
   explicitly typed zero to `= 0`; all hypotheses, conclusions, definitions,
   and existing declaration signatures are otherwise unchanged. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles without errors, warnings,
   `sorry`, or forbidden declarations. The proof uses only the declared Ext
   effacement dependency and the imported Mathlib site APIs. Verdict: pass.
3. The direct witness conclusion is true and exactly matches the construction:
   `E` is the Type-v subtype of generator/lift pairs, `f` is locally surjective,
   and the displayed Ext pullback vanishes. No split-off statements or new nodes
   were added, and the search found no existing theorem duplicating this result.
   Verdict: pass.
4. The proof follows the shortest available route through
   `Ext.exists_epi_comp_eq_zero`, the image-subsheaf local-surjectivity argument,
   and the free-sheaf lift. Imports are all used; no pruning is available. The
   DAG proof and dependency list agree with the Lean proof, and the unit route
   remains realized by the witness and caller declarations. Verdict: pass.
5. The witness node's Lean statement now exactly matches the normalized source;
   its proof steps, dependency, source, and unit metadata agree with the module.
   The caller applies the witness directly, so no downstream adaptation is
   required. Verdict: pass.

Changed only the normalized equation and its node statement, and added this
second-reader record. No holes were closed or added, and no imports or nodes
were pruned.
