## What changed
The target module now proves additivity directly from the existing finite-limit theorem and the standard zero-morphism and binary-product lemmas. The remaining target clauses are split into two sibling modules: the adjunction component formula and the unit-induced stalk properties. The target combines these three results. Imports are proof-only sibling imports where possible.

## Proved and sorry left
The target `AlgebraicGeometry.Scheme.Modules.module_extensionByZero_adjunction` compiles and is proved by combining the three component results. The two new component theorems retain named `sorry` proofs: `module_extensionByZero_hom_formula` and `module_extensionByZero_unit_stalks`; each has its own node and complete source proof plan. No `sorry` remains in the target proof itself.

## No longer needed
The invalid `module_extensionByZero_remainder` helper and its attempted projection were removed. The earlier monolithic helper declarations were replaced by the two strict component nodes. No imported module is unused by the compiling proof.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt treated `∃ adj, True` as if it projected to the requested adjunction and failed with `projNonPropFromProp`. The exact adjunction available from `open_restriction_adjunction_exact` supplies only a `Nonempty` witness and does not state the target's component formula or stalk equations, so those clauses require separate intermediate statements.

## Earlier second reading (a previous round; superseded)
The sibling modules and their nodes remain open for the second reader. Their statements are strict parts of the target: one supplies only the component formula, and one supplies only the stalk and naturality clauses for a supplied adjunction.

## Second reading by T3
1. **Unchanged visible statements.** I diffed the delivered target against the repository version. The target theorem signature is byte-for-byte unchanged; only its proof, proof-only imports, and proof records changed. The sibling theorem signatures agree with their node `lean.statement` fields.

2. **Compilation and trust.** I compiled all three modules in dependency order with `lcompile.py --all`; all compiled without warnings. The two sibling proofs remain the named `sorry`s listed above, and no `sorry` occurs in a definition or anonymous proof. The target proof itself has no `sorry`.

3. **Statements and split nodes.** The component nodes are strict parts of the target: HomFormula asserts only the adjunction component equation, while UnitStalks asserts only the zero-outside, interior stalk, scalar, and naturality clauses for a supplied adjunction. I corrected their node descriptions from imperative proof recipes to propositions matching the declarations. Searches found no existing extension-by-zero module adjunction.

4. **Pruning and route.** The proof uses every target import, including the exact open-restriction theorem needed for preservation of finite limits and both sibling modules. The invalid remainder/projection helper is absent. I added the exactness node to `proof_deps` because its declaration is used directly. The unit route is retained; this is below-unit decomposition only.

5. **DAG agreement.** The target node's proof and `proof_deps` name the exactness theorem and both component nodes. The new node records, Lean declarations, source references, and named sorry proofs agree with the delivered modules. No definition or target statement changed.

The second reading changed the two new node statements from proof-method descriptions to precise result statements, added the exactness dependency to the target record, and updated the proof-plan text accordingly.

## New nodes
`lem-weil-pbc-module-extension-by-zero-hom-formula` records the direct-sum/sheafification Hom formula and is realized by `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula`. `lem-weil-pbc-module-extension-by-zero-unit-stalks` records the zero-outside, isomorphism-inside, scalar, and naturality stalk clauses and is realized by `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroUnitStalks`.
