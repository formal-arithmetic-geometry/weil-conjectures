## What changed

Completed all three proofs in `lean/Sheaf/AlgebraicGeometry/AssociatedModule.lean`.
Every existing signature, definition, public visibility, and import is unchanged.

- `AlgebraicGeometry.associatedExtension_restriction_existsUnique`: presheaf composition
  makes the ring restriction R-linear for the two explicit restricted module structures.
  Apply `TensorProduct.map` to that linear map and the identity of M. Tensor induction
  proves linearity into the restriction of scalars. The defining pure-tensor formula is
  definitional, and `ModuleCat.ExtendScalars.hom_ext` proves uniqueness.
- Added the proved private helper `associatedExtensionRestriction_tmul`, which extracts
  the pure-tensor formula from the chosen map's specification. It is used only by proofs.
- `AlgebraicGeometry.associatedExtensionRestriction_laws`: apply scalar-extension
  extensionality to `1 ⊗ m`, then the restriction formula. The scalar-restriction identity
  and composition isomorphisms act identically on elements.
- `AlgebraicGeometry.associatedModulePresheafMap_naturality`: scalar-extension
  extensionality and the pure-tensor formulas for restriction and base change identify
  both composites.

This implements the existing node's steps 1 and 4 directly; the existing sheafification
and canonical-section proofs supply steps 2, 3, 5, and 6. No route, node, statement, or
interface change is needed. The unit `sk-thm-p1` route is unchanged.

Searches via `msearch.py`: LeanFinder for scalar-extension maps along compatible ring
homomorphisms found `ModuleCat.ExtendScalars.map_tmul` and tensor-map APIs; Loogle for
`TensorProduct.map` found the map and its pure-tensor formula; grep for
`restrictScalarsComp|fromExtendScalars` found the change-of-rings API. Local searches
also read `PresheafChangeOfRingsAdjunction.lean` and Mathlib's `ChangeOfRings.lean`.
The direct tensor construction preserves the original theorem's unrestricted module
universe; the categorical adjunction API imposes a larger module universe.

Checked the source constructions at Stacks [01BH](https://stacks.math.columbia.edu/tag/01BH)
(3), functoriality assertion (2), and [01BI](https://stacks.math.columbia.edu/tag/01BI).
Edge cases (empty space/opens, zero ring/module, identity inclusions) use exactly the same
construction: no nonemptiness, nonzero, or strict-inclusion hypothesis occurs.

Validation: the complete module compiles without warnings through `lcompile.py`.
The delivery dry run also checks declaration signatures and axioms.

## Proved and sorry left

Closed 3 of the 3 original holes, all on node `def-weil-pbc-associated-module`:

- `AlgebraicGeometry.associatedExtension_restriction_existsUnique`.
- `AlgebraicGeometry.associatedExtensionRestriction_laws`.
- `AlgebraicGeometry.associatedModulePresheafMap_naturality`.

No sorry remains in the item's module. No holes were added or split off. This is a
proof, not a decomposition; its imports are Mathlib modules only.

## No longer needed

None. Both existing public imports supply definitions and types used by the file.
No proof-dependency import was added or removed. No DAG node or module is newly pruned;
the existing mathematical plan is implemented directly using Mathlib tensor products.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's inability to construct the restriction map is resolved by the
R-linear ring restriction, `TensorProduct.map`, and tensor induction. It was not a
mathematical obstruction. No defect in the statement, DAG plan, or unit route was found.

## Second reading by P1

1. **Visible changes.** Compared the delivered module with the repository version. Existing
   declaration signatures, definitions, visibility, and imports are byte-for-byte unchanged;
   only the three named proofs and one private proof helper were added.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds without warnings.
   The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
   The remaining `sorryAx` seen when printing axioms comes from the repository's still-open
   declarations in the imported compiled module, not from these proofs.
3. **Split statements.** No statements were split off and no new nodes were added. The helper
   is private, proved, and is exactly the pure-tensor consequence of the existing uniqueness
   theorem; it introduces no public interface or hole.
4. **Pruning and route.** Both public imports are used for the module's definitions and types,
   so no import can be removed. The proofs follow the existing tensor-extension route and keep
   the `sk-thm-p1` unit route and its realized nodes.
5. **DAG agreement.** The existing node `def-weil-pbc-associated-module` still names the same
   module and declarations; its statement and proof dependencies are unchanged. The three
   closed declarations are exactly the three holes listed in the delivery report.

I changed only this report section; no Lean, DAG, or change-record repair was needed.
