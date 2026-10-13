## What changed
Imported `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverseBijective` and proved the target inverse theorem by converting the bijective underlying additive homomorphism to an `AddEquiv`, then packaging its inverse as an `AddCommGrpCat` morphism. Added the bijectivity intermediate theorem module with its planned proof left as `sorry`.

## Proved and sorry left
Closed `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_inverse`. Left `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_bijective` as the single named sorry, with node `new-etale-affine-singleton-tensor-degree-comparison-bijective`.

## No longer needed
No imports or DAG dependencies were pruned; all existing imports remain available for the stated route.

## Where the brief, the DAG or earlier work was wrong
The inverse construction requires an explicit bijectivity substatement; the original node's proof plan omitted this separately stated intermediate. The decomposition is strictly simpler and the categorical inverse identities are proved directly.

## New nodes
`new-etale-affine-singleton-tensor-degree-comparison-bijective` is stated in `lean/Sheaf/AlgebraicGeometry/EtaleAffineSingletonTensorDegreeInverseBijective.lean`; no change record is needed.

## Earlier second reading (a previous round; superseded)
The inverse theorem has unchanged signature and is proved from the bijectivity intermediate; the new statement is strictly simpler and matches the affine calculation substep. The unit route through the normalized comparison is retained.

## Second reading by N1

1. **Visible changes.** Compared the delivered target module with the repository version. The existing theorem signature is byte-for-byte unchanged. The only interface additions are the explicitly split bijectivity theorem and its new module, recorded by the new DAG node; no target or existing declaration was weakened.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The inverse proof uses `AddEquiv.ofBijective`, constructs the inverse morphism, and proves both categorical identities by extensionality. The remaining `sorry` is exactly the named public theorem `singletonTensorDegreeComparisonHom_bijective`, with its docstring, blueprint reference, and node. No definition contains `sorry`, and no forbidden declaration was added.

3. **Split statement.** Checked the new bijectivity statement against the affine tensor calculation route and the normalization predicate. It is a strictly simpler intermediate required by the inverse construction, with the exact hypotheses and conclusion needed; it does not restate the inverse target. Its source, proof sketch, searches, and Lean declaration agree with the new node.

4. **Route and pruning.** The unit route through the normalized comparison is retained. Tested removing the four proof-only imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, `Sheaf.AlgebraicGeometry.EtaleTensorSections`, and `Sheaf.AlgebraicGeometry.TensorPullback`; both modules still compile, so these imports and their corresponding unused dependencies are pruned.

5. **DAG agreement.** The target node's proof and dependencies now reflect the split bijectivity step, and the new node records the theorem's statement, source, proof origin, searches, and module. No unit record change is needed.

Changed the target module to remove the four unused proof-only imports and appended this second-reading record. No theorem statements or definitions were otherwise changed.
