## What changed
Split the construction into two strictly simpler intermediate theorems and proved the target by combining them. Added imports for the two new modules.

## Proved and sorry left
The target `exists_affine_depth_two_locally_free_model` is proved from `exists_affine_locally_free_model_core` and `affine_depth_two_boundary_property`. The two intermediate theorems retain named `sorry`s, with nodes `new-affine-locally-free-model-core` and `new-affine-depth-two-boundary-property`.

## No longer needed
No imports or planned nodes were pruned; the target's existing extension dependency remains available for the split theorem.

## Where the brief, the DAG or earlier work was wrong
The original proof plan combines extension and depth-two kernel calculations in one theorem; these are independent substantial arguments, so they were split into two named nodes.

## New nodes
`new-affine-locally-free-model-core` and `new-affine-depth-two-boundary-property`, as recorded in the sandbox DAG copies.

## Earlier second reading (a previous round; superseded)
The target proof compiles and preserves its original signature. The two new statements are strictly simpler components: extension with restriction and the boundary depth property.

## Second reading by M3

1. **Interface unchanged.** Compared the delivered target module with the repository version; the theorem signature and all existing declarations are byte-for-byte unchanged. The two added modules contain only new split declarations recorded by matching DAG nodes.

2. **Compilation and proof audit.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`, while the two split-off intermediate theorems retain exactly their named `sorry`s. No forbidden axioms, unsafe declarations, or hollow definitions were added.

3. **Split statements and nodes.** Checked both intermediate statements against their declarations and DAG records. They are strictly simpler components of the target (extension core and boundary depth property), with source/docstrings and matching node metadata; no duplicate library theorem was found.

4. **Route and pruning.** The target proof applies the extension-core theorem and then the boundary-depth theorem, preserving the target's construction route. Removed the target's unused imports of `ModuleFinitePresentationExtension` and `Mathlib.AlgebraicGeometry.Modules.Tilde`; removed a duplicate sheaf import in the core module. The target node proof dependencies now name the two declarations actually used.

5. **Verification verdict.** The proof establishes the original target unchanged, and the remaining holes are explicit, named, and documented. The unit route is retained through the two decomposition nodes.

Changed in this second reading: pruned three unused/duplicate imports, synchronized the target DAG proof dependencies and origin with the implemented proof, and added this review record.
