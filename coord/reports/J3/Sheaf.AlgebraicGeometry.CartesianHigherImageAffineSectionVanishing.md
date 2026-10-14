## What changed

Proved `exists_cartesianHigherImage_affine_section_eq_zero` by reducing the final equality to a finite affine etale cover and applying sheaf separatedness. The finite-cover glue is proved in `cartesianHigherImage_section_eq_zero_of_finite_cover`. The cohomology-continuity and affine-descent portion is isolated as `exists_cartesianHigherImage_affine_section_local_zero` in a new module.

## Proved and sorry left

Proved: `exists_cartesianHigherImage_affine_section_eq_zero`; `cartesianHigherImage_section_eq_zero_of_finite_cover`.

Sorry left: `exists_cartesianHigherImage_affine_section_local_zero`, blueprint `lem-sc-cartesian-higher-image-affine-section-local-vanishing`. This is strictly weaker than the target: it only supplies a later stage and a finite etale cover with zero restrictions.

## No longer needed

The target no longer directly needs the three original proof-dependency imports; the implemented route uses the new local-vanishing module and `CartesianHigherImageTransitions`. The original cohomology and comparison nodes remain proof dependencies of the split local theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG combined cohomology-presheaf lifting, affine descent, and continuity into one proof step without a Lean declaration exposing the required cartesian comparison. That step is now isolated as the new local theorem, while the finite-cover sheaf glue is complete.

## New nodes

`lem-sc-cartesian-higher-image-affine-section-local-vanishing`: local affine-cover vanishing, stated in `lean/Sheaf/AlgebraicGeometry/CartesianHigherImageAffineSectionLocalVanishing.lean` and left with one documented `sorry` for a subsequent worker.

## Second reading by J3

1. **Repository comparison — pass.** The target declaration
   `exists_cartesianHigherImage_affine_section_eq_zero` has the same hypotheses and
   conclusion as the repository version. The only target-module change is its proof
   import cleanup; the new local theorem is a separate declaration and node.
2. **Compilation and proof status — pass.** Both sandbox modules compile with
   `lcompile.py --all`. The target proof has no `sorry`; the only remaining `sorry` is
   the named theorem `exists_cartesianHigherImage_affine_section_local_zero`, with its
   source, blueprint tag, and node recorded above. The finite-cover glue proof is
   kernel checked and uses only ordinary category and sheaf APIs.
3. **Statement and split review — pass.** The local theorem is strictly weaker than
   the target: it supplies a later transition and a finite cover with zero
   restrictions, while the target concludes global vanishing. Its finite-family
   binder uses `[Finite J]`, which is exactly what the cover argument needs; the
   target still requests the stronger `[Fintype J]` witness. No duplicate upstream
   theorem was found.
4. **Pruning and route — pass.** The target now imports only the local-vanishing
   module (and its public transition dependency); the direct `AffineEtale` import was
   removed. The three former continuity/comparison imports remain recorded as proof
   dependencies of the split local theorem. The finite-cover separatedness route and
   the unit `sk-thm-vanishing` route are preserved.
5. **DAG agreement — pass.** The target node now lists the local-vanishing node as
   its sole proof dependency, and the new node records its module, declaration,
   source, proof plan, unit, and split status. The node statements match the Lean
   declarations.

Changed in this second reading: removed the now-unused direct `AffineEtale` import
from the target module, renamed the unused cone-limit binder to `_hc`, and generalized
the finite-cover helper's internal witness from `[Fintype J]` to `[Finite J]` to remove
lint warnings without changing the target interface.
