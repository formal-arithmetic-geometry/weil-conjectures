## What changed

Added `Sheaf.CategoryTheory.DerivedModuleRankOneNonzeroMap` and reduced `derivedModule_rankOne_generator` to its existence statement.

## Proved and sorry left

`derivedModule_rankOne_generator` is proved. `derivedModule_rankOne_nonzero_map` remains sorry; it isolates the representative, cohomology, and localization argument.

## No longer needed

No imports or planned nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The direct plan omits the substantial derived-category API needed to construct the nonzero morphism. The missing argument is isolated as one strictly simpler theorem.

## New nodes

Added `new-stage3-derived-module-rank-one-nonzero-map` and its module.

## Earlier second reading (a previous round; superseded)

The reduction unfolds the definition and applies the new existence statement pointwise; the remaining sorry is strictly below the target and has the required source and proof plan.

## Second reading by H4

1. Compared the delivered generator module with the repository version. The theorem signature is byte-for-byte unchanged; only a proof and a proof-only import were added. The new nonzero-map theorem is a separate, strictly simpler statement with its own node.
2. Compiled both delivered modules individually and together with `lcompile.py`; compilation succeeds. The only remaining `sorry` is the named theorem `derivedModule_rankOne_nonzero_map`; no definitions contain `sorry`, and no forbidden declarations were added.
3. Checked the split statement against the target definition: it is exactly the pointwise existence clause needed after unfolding `IsWeakTriangulatedGenerator`, with the same hypotheses and conclusion. Its docstring gives the source and complete intended argument, and its DAG node matches the Lean declaration. No existing Mathlib or project declaration duplicates it.
4. Checked the proof route and pruning. The generator proof uses the split theorem pointwise and preserves the unit route. Removed the unnecessary public import of `Sheaf.CategoryTheory.WeakTriangulatedGenerator` from the split theorem's module; the target module still imports it for its statement.
5. Checked the DAG proof and dependency records: the generator node now records the split theorem as its sole proof dependency, and the new node records the remaining hole and its source. The unit and chapter fields are unchanged.

Changed the split module's imports, added this second-reading record, and retained the one unavoidable lower-level `sorry`.
