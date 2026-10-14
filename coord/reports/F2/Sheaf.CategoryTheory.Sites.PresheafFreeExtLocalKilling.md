## What changed

Copied the existing complete proof of `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing` into the F2 sandbox for delivery. The proof constructs a locally surjective presheaf cover and lifts the Ext-killing factorization through the free abelian sheaf.

## Proved and sorry left

Both declarations are proved. No `sorry` remains.

## No longer needed

No imports or DAG dependencies were removed; all imports used by the existing proof remain necessary.

## Where the brief, the DAG or earlier work was wrong

The module had already been landed with a complete proof before this worker started. No discrepancy was found.

## Earlier second reading (a previous round; superseded)

The copied proof compiles, has no `sorry`, and preserves both declaration signatures.

## Second reading by F2

1. **Interface and accidental changes.** Compared the delivered module with the repository version. Both public theorem signatures and all definitions are byte-for-byte unchanged; the only textual difference is harmless parenthesization in the proof of the private helper `epi_locally_surjective`.

2. **Compilation and axioms.** Compiled the module with `lcompile.py` successfully. A scratch copy with `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for both public declarations. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.

3. **Statements and dependencies.** Checked both declarations against their DAG nodes and the imported effacement theorem. The witness theorem provides exactly the presheaf, locally surjective map, and vanishing equation; the wrapper theorem is a direct application and adds no weakening or extra hypothesis. The split-off effacement node is a genuine lower-level dependency, not a restatement. No duplicate library theorem was found.

4. **Route and pruning.** The proof follows the recorded unit route: epimorphic Ext effacement, locally generated image subsheaf, explicit lifting presheaf, and Ext composition. The imports are appropriate: the two `Mathlib` imports support public statement types, while `ExtEpiEffacement` is proof-only and is correctly a plain import. No old proof dependency or import is unused, so nothing is pruned.

5. **Nodes and unit.** The DAG proof steps and `proof_deps` agree with the Lean proof, including the dependency on `lem-sc-ext-epi-effacement`; the unit `sk-prop-cd` route remains realized. No new statements or nodes were added.

Changed: only this second-reading record; no Lean repair was needed.
