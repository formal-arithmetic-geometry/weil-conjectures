## What changed
Added the core unit-transport intermediate theorem and used it to prove `schemeMV_image_composition_localization` by functoriality of `R.map`.

## Proved and sorry left
`schemeMV_image_composition_localization` is proved. `schemeMV_image_composition_localization_core` remains a named intermediate theorem with `sorry`, recorded in the new DAG node.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The detailed categorical transport in the blueprint could not be completed directly in the available session, so it was split at the final derived-map factorization boundary.

## New nodes
`lem-pc-mayer-vietoris-image-composition-localization-core` records the strict intermediate unit-transport identity.

## Second reading by N4

1. **Interface and accidental changes.** I compared the delivered module with the repository version. The existing declaration `schemeMV_image_composition_localization` has the identical signature and statement; the only interface addition is the explicitly split core theorem recorded by the new node. The restriction-localization-chain module is byte-for-byte unchanged.
2. **Compilation and proof audit.** Both sandbox modules compile with `lcompile.py --all`; the only diagnostic is the existing long-line style warning. The target proof contains no `sorry`; the sole remaining `sorry` is the named theorem `schemeMV_image_composition_localization_core`, with its docstring and DAG node. No forbidden declarations or hollow definitions were added.
3. **New statement.** The core theorem is a strict intermediate equation: it has the restriction chain and inverse comparison as separate factors, while the target combines them under `R.map`. It is therefore strictly simpler than the target and is exactly what the target proof invokes. Its source, proof sketch, statement, and Lean attachment agree in the new node.
4. **Pruning and imports.** `public import Sheaf.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain` is required by the public signatures; the normalization module is used by the proof context and remains a plain import. No unused import or proof dependency was found.
5. **Unit route and DAG consistency.** The proof keeps the unit's explicit restriction-localization chain and updates the target node's `proof`, `proof_deps`, and `proof_origin` to record the core theorem plus `Functor.map_comp` reassociation. The core node remains attached to the same unit.

Changed in this reading: updated the existing target DAG node to match the factored Lean proof, and added this second-reading audit. No mathematical declaration was changed.
