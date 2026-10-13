## What changed

Closed the original theorem by constructing the induced residue-field algebra structure and reducing the remaining affine construction to the new named theorem `exists_reduced_generic_fibre_map_core`. Added the proof-only import of `Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore`.

## Proved and sorry left

The original declaration `AlgebraicGeometry.exists_reduced_generic_fibre_field_embedding_core` is proved. One strictly smaller intermediate theorem remains as `sorry`: `AlgebraicGeometry.exists_reduced_generic_fibre_map_core`, node `lem-sbc-reduced-generic-fibre-field-embedding-core-map`.

## No longer needed

No imports were removed. The direct proof does not separately formalize the tensor-product and localization steps; those are isolated in the new intermediate node.

## Where the brief, the DAG or earlier work was wrong

The original plan combines the affine tensor, reduction, localization, and Spec arguments into one very large theorem. These are split into a strictly smaller dominant-map theorem so the top-level algebra compatibility is proved directly.

## New nodes

`lem-sbc-reduced-generic-fibre-field-embedding-core-map` states the dominant map and base-composite portion of the affine construction. Its source is Stacks Project Tags 0559 and 030R; LeanFinder, Loogle, and repository grep found only component lemmas, so the sourced affine argument remains open.

## Earlier second reading (a previous round; superseded)

The top-level theorem signature is unchanged and compiles. The new map theorem is a strict sub-conclusion, with the algebra structure supplied as an explicit argument; its remaining affine tensor and localization proof is documented in its docstring and node. Both modules compile in import order. The only remaining `sorry` is the named public intermediate theorem, and no definition contains a hole.

## Second reading by B4

1. I compared both delivered modules with the repository versions. The existing target theorem signature is byte-for-byte unchanged; the only existing-module changes are a proof-only import and proof body. The new map theorem is a separate strict sub-conclusion with the explicit induced algebra structure.

2. Both modules compile in import order with `lcompile.py --all`. The only remaining `sorry` is the named split theorem `AlgebraicGeometry.exists_reduced_generic_fibre_map_core`; there are no axioms, unsafe declarations, hollow definitions, or unnamed holes in the delivered files. The target proof uses only the permitted construction and the split theorem.

3. The split theorem is true as the affine tensor, reduction, localization, and spectrum construction described in its docstring, and is strictly smaller than the target because its algebra structure is an explicit argument and it omits the final residue-field compatibility conjunct. Repository and Mathlib searches found no existing declaration of this result. Its DAG node and statement match the Lean declaration.

4. The proof follows the unit route through the affine map construction; no proof-dependency import can be pruned. The plain import of `ReducedGenericFibreMapCore` is proof-only, while the statement imports remain public. The unit `sk-prop-normal-form` remains realized by the target and split map node.

5. The DAG proof and `proof_deps` agree with the Lean proof: the target invokes the split map theorem and then proves the compatibility by reflexivity; the split node records the documented affine construction and has no undeclared dependencies.

I changed only this report section; no theorem statements or definitions were changed.
