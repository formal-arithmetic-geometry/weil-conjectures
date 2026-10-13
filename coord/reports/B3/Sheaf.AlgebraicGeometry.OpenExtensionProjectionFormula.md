## What changed

The target proof now reduces to two named intermediate theorems. `OpenExtensionDerivedAdjunction` states existence of the transported derived extension adjunction, and `OpenExtensionProjectionFormulaAux` states invertibility of the projection mate for any such adjunction. The target combines them by a complete Lean proof. Imports were added for these two modules.

## Proved and sorry left

The target declaration `AlgebraicGeometry.exists_openExtension_projectionFormula` is proved. The two strict intermediate declarations remain `sorry`: `AlgebraicGeometry.exists_openExtension_derivedAdjunction` and `AlgebraicGeometry.openExtension_projection_formula_of_adjunction`.

## No longer needed

Removed the direct proof-only imports `Sheaf.Algebra.Homology.KFlatResolution`, `OpenRestrictionAdjunctionExact`, `KFlatStalkCriterion`, and `ModuleStalkExact` from the target and both split modules. The target proof uses only the two split declarations; their signatures use only `DerivedTensorStructure`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan requires substantial derived localization and stalkwise support arguments not exposed by the imported interfaces. These were split into the two strict intermediate statements above.

## New nodes

`lem-pc-open-extension-derived-adjunction` records the transported derived adjunction intermediate theorem. `lem-pc-open-extension-projection-aux` records the conditional projection-mate theorem.

## Second reading by B3

1. **Interface check.** Compared the delivered target with the repository version. The target signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports changed. The two added declarations are separate named intermediate theorems.

2. **Compilation and axioms.** Compiled all three sandbox modules with `lcompile.py --all`. The target has no `sorry`; the two split declarations are the only named `sorry`s and have source, proof outlines, and nodes. No forbidden declaration forms were added.

3. **Statements and nodes.** Checked that the target applies the derived-adjunction theorem and then the projection-mate theorem with exactly the target's `J`, `adj`, `A`, and `K`. The intermediate statements are strictly smaller than the target and their node metadata now contains self-contained statements and proof dependencies matching the declarations.

4. **Pruning and route.** Removed four unused homology imports from each affected module. The open-extension unit route is retained through the two intermediate nodes; no unit or chapter metadata changed.

5. **DAG consistency.** Updated the target node proof and `proof_deps` to the two declarations actually used by the Lean proof. Updated both split nodes' proof steps and dependencies to match their documented arguments. No target statement or definition changed.

The second reading changed only proof-only imports, proof metadata, and the new-node metadata; no additional hole could be closed safely in the review.
