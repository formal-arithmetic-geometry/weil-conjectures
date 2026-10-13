## What changed

Proved the target theorem by constructing the three canonical model maps from the universal derived-functor model-map theorem. The target proof now reduces the remaining exact-row construction and boundary transport to two named intermediate statements. The boundary-square intermediate is proved using counit shift naturality, comparison_eq, and faithful restriction. Added proof-only imports for the model-map and coherent-shift infrastructure.

## Proved and sorry left

Closed `ModuleCat.exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows` in the item module (one original hole closed). Added two lower holes: `ModuleCat.baseDerivedExtension_coherent_triangle_distinguished` and `ModuleCat.exists_baseDerivedTensor_canonical_row_completion`. This is a decomposition, not a completed proof; the net hole count is -1. Proved the new `ModuleCat.baseDerivedTensor_ordinary_boundary_square` without a new hole. The following strictly smaller intermediate statements remain sorry and are supplied as separate modules: `ModuleCat.baseDerivedExtension_coherent_triangle_distinguished` and `ModuleCat.exists_baseDerivedTensor_canonical_row_completion`. The latter is the exact-row construction from the universal counit; the former is the triangulatedness of the coherent universal derived extension.

## No longer needed

No old module imports were removed or modules pruned. The old direct proof dependency `lem-pc-base-derived-extension-resolution` is now used through `lem-pc-base-derived-extension-coherent-triangle`, rather than directly by the target. The target node records the model-map, coherent-shift, canonical-row and boundary-square dependencies actually used. Removed unused `Mathlib.Algebra.Homology.ExactSequence` imports from the new coherent-triangle and boundary-square modules.

## Where the brief, the DAG or earlier work was wrong

The first worker omitted the boundary-square node, full Lean signatures and statement dependencies for the new nodes, their recorded searches, and the target node update. These metadata omissions were repaired by the second reader. The DAG proof plan omitted an explicit statement that the coherent universal derived extension sends the restricted distinguished triangle to a distinguished triangle. It also omitted the tensor-linear exact-row completion as a separate intermediate theorem. These are recorded as new nodes below.

## New nodes

`lem-pc-base-derived-extension-coherent-triangle` is stated in `BaseDerivedExtensionCoherentTriangle.lean`; its proof is the triangulated derived-extension argument described in its docstring.

`lem-pc-base-derived-tensor-canonical-row-completion` is stated in `BaseDerivedTensorCanonicalRowCompletion.lean`; its proof is the universal-counit identification, tensor induction for the boundary map, and transport of the long exact row described in its docstring.

`lem-pc-base-derived-tensor-ordinary-boundary-square` records the proved boundary-square theorem in `BaseDerivedTensorOrdinaryBoundarySquare.lean`. There are three new nodes, of which two remain open.

## Second reading by S4

1. Compared the delivered target module with the repository version. The target theorem
   signature and all existing declarations are unchanged; only proof imports, private proof
   helpers, and the target proof were added. The two split statements are new declarations with
   matching DAG nodes.
2. Compiled all four delivered modules with `lcompile.py --all`. There are no compiler errors,
   forbidden declarations, or `sorry` in definitions. The only remaining `sorry`s are the two
   named split theorems listed above. Their documentation states the source and the complete
   intended proof route. The long-line linter warning was repaired in this reading.
3. Checked both split statements against their declarations and searched the library for existing
   duplicates. Each is a strictly smaller intermediate claim: coherent triangulatedness and the
   canonical exact-row completion. Neither weakens the target or merely restates it.
4. Read the proof from the target downward. The target uses the model-map theorem, canonical row
   completion, and boundary-square theorem; the unit route through the universal derived model is
   retained. The unused ExactSequence imports in two new modules were removed. No old module was pruned. The unit realization lists no additional mandatory nodes for this item.
5. Checked the DAG records for the target and both split nodes. Their declarations, statements,
   proof descriptions, dependencies, source, chapter, and unit agree with the delivered Lean.

Repaired the long line, localized the proof-only ChangeOfRings scope in the target, removed two unused imports, completed new-node metadata and signatures, added the missing proved boundary-square node, and updated the target proof route. Independent leanfinder, loogle and grep searches found generic triangulated-functor and exact homology sequence infrastructure, but no duplicate of either split statement. The zero-ring and zero-complex cases reduce to zero exact rows; arbitrary shifts and nonflat extensions are handled by the derived functor rather than ordinary exactness. No existing theorem statements or definitions were changed. Explicit #print axioms in a scratch copy confirmed that the proved boundary-square theorem uses only propext, Classical.choice and Quot.sound; the target and the two split theorems additionally use sorryAx. The scratch file was removed. deliver3.py also probes every delivered constant.
