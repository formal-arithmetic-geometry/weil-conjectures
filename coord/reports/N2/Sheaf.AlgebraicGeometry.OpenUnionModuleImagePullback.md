## What changed
Replaced the rejected universal-property restatement with a sectionwise element-level gluing theorem and a separate assembly theorem. The target pullback theorem applies these two lower statements.

## Proved and sorry left
`AlgebraicGeometry.schemeOpenUnionModuleImage_isPullback` is proved from the two intermediate declarations. `AlgebraicGeometry.schemeOpenUnionModuleImage_sectionwise_gluing` remains `sorry` for the two-open sheaf gluing argument. `AlgebraicGeometry.schemeOpenUnionModuleImage_isPullback_of_sectionwise` remains `sorry` for the naturality/module-sheaf assembly argument.

## No longer needed
The previous `schemeOpenUnionModuleImage_pullback_universal` declaration and its expanded pullback universal-property formulation are removed. No imports were otherwise pruned.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt split off the complete pullback universal property under another name. The replacement separates the genuinely sectionwise gluing step from the categorical assembly step.

## New nodes
`lem-pc-open-union-module-image-pullback-core-sectionwise` and `lem-pc-open-union-module-image-pullback-core-assembly`.

## Second reading by N2

1. **Diff and interfaces.** Compared both delivered Lean modules with the repository versions. The target theorem signature is unchanged. The two split-off declarations are new and their node records now contain their complete Lean statements. Verdict: pass.

2. **Compilation and proof hygiene.** Compiled both modules with `lcompile.py --all`; compilation succeeds. The target proof has no `sorry`; the two explicitly named intermediate theorems remain the only sorry declarations. No forbidden axioms, definitions with sorry, or unsafe declarations were added. Verdict: pass.

3. **Statements and nodes.** Checked the sectionwise statement and the assembly statement against the source declarations. They are true intermediate obligations, strictly below the target, and each has a source, docstring, and DAG node. The earlier universal-property restatement is absent. Verdict: pass.

4. **Pruning and route.** The target now uses the sectionwise and assembly nodes. The sectionwise module imports the section-restriction lemma as a proof-only import. The target module no longer imports that lemma directly; its proof-only dependency is the core module. Verdict: pass; this is the complete import pruning found on review.

5. **Unit route and DAG agreement.** The parent node proof and `proof_deps` now record both intermediate nodes, and each intermediate node records its actual declaration and dependency route. The unit's open-union gluing route is retained. Verdict: pass.

Changed during second reading: removed the redundant direct section-restriction import from the target module, added it privately to the core proof module, shortened overlong lines, added the parent node's updated proof metadata, and replaced abbreviated node Lean statements with complete signatures.
