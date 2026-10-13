## What changed

Repaired the duplicate-proof return for
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient`.
Added proof-only `import all Sheaf.AlgebraicGeometry.CoherentFormalModule` alongside
its unchanged public import. This exposes the existing private lemmas to this proof
without changing their visibility or editing their module.

Removed all seven duplicate private declarations:
`idealModuleProduct_quasicoherent`, `quotient_iterated`,
`quotient_multiplication_naturality`, `quotient_product_comp_zero_iff`,
`quotient_product_epi_comp_zero_iff`, `quotient_product_mono`, and
`quotient_product_zero`. The main proof now directly uses the existing
`idealModuleProduct_quasicoherent`, `formalModuleQuotient_iterated`, and
`idealModuleProduct_quotient_zero`; the other four helpers are internal to their
existing proofs and need no local replacements.

Retained the finite-generator descent and scalar-annihilation arguments. The public
theorem signature, existing docstrings, and concrete quotient functor definition are
unchanged. Updated the node's proof, proof_deps and proof_origin to match the reuse.
No other module is edited; no statement or interface change is made.

Validation: the repaired single-file proof compiles cleanly. The final delivery dry
run checks compilation, declaration axioms and preflight; no push is requested.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherentFormalModules_affine_quotient_coherent`
(node `lem-weil-pbc-coherent-formal-modules-affine-quotient`).

Holes added: none. Sorries left in delivered modules: none. The two remaining private
helpers, `scalar_zero_of_product_zero` and `finite_of_completion_generators`, are
proved. The unchanged quotient functor uses the completed theorem. This is a proof,
not a decomposition into new holed statements.

The finite-generator argument includes k=0, I=0, I=top and the zero module without
assuming injectivity of the completion map. The reused quotient results include
exponent zero and equal exponents.

## No longer needed

The second reader additionally removed redundant proof imports
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`, verified by compilation.
Their declarations remain available through retained imports; no corresponding
proof dependency or target-closure module is removed.

Removed added proof imports:
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` and
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`.
Their local uses belonged to the seven deleted duplicate proofs. The previous
reading had also removed redundant added imports
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

Removed direct proof dependencies
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections` and
`lem-weil-pbc-quasi-coherent-module-kernel`: the main proof uses the existing
quasi-coherence helper rather than proving its tensor/kernel argument again. These
results remain transitive dependencies of CoherentFormalModule; this repair claims
no removal of those modules from the targets' import closure.

All original imports remain. No blueprint unit statement or step is bypassed.
No new helper module is introduced. The explicit module/sheaf quotient comparison
isomorphism remains unnecessary: top-section surjectivity and annihilation suffice.

## Where the brief, the DAG or earlier work was wrong

The previous delivery and its second reading incorrectly treated the private
CoherentFormalModule lemmas as unavailable. Lean's `import all` permits reuse of
exactly these existing declarations. The seven duplicated statements identified
by import_prune_check are removed, rather than renamed or restated.

The public `formalCompletionSystem_coherent` still requires the original sheaf to
be coherent, which need not hold after restriction from the completion. The
remaining finite-generator argument establishes coherence at each quotient level.
No mathematical statement error or forced adaptation was found.

## Second reading by J1

1. PASS: compared the delivered module with the repository using diff, then checked
   the public theorem signature and the entire quotient-functor definition byte for
   byte. Both are unchanged; the public imports and existing docstrings are unchanged.
   Only this module and its node's proof metadata are delivered; no change record or
   forced adaptation is needed.
2. PASS: independently compiled the module with lcompile.py without warnings. A fresh
   scratch copy printed axioms for scalar_zero_of_product_zero,
   finite_of_completion_generators, coherentFormalModules_affine_quotient_coherent,
   and coherentFormalModules_affine_quotientFunctor: each uses only propext,
   Classical.choice and Quot.sound. No sorry, forbidden declaration, or hollow
   definition occurs. The functor remains the concrete ObjectProperty.lift.
3. PASS: no statements are split off, no new holes or nodes are added. Read both
   proved private helpers: evaluating the zero multiplication morphism on a pure
   tensor gives scalar annihilation; completion evaluation and span induction give
   finite-generator descent. For k=0 or I=top, the annihilation hypothesis forces
   the target module to be zero; I=0 and the zero module also fit the argument.
   Independent Loogle and Lean Finder searches for completion-module finiteness
   returned completion exactness/tensor-product results, not this descent assertion.
   Searched the project for annihilation and completion-quotient arguments; reused
   CoherentFormalModule's existing private quotient results rather than duplicating
   them. No arbitrary data is selected from an unproved existence statement.
4. PASS after import pruning: read from the top theorem through coherence,
   top-section surjectivity, scalar annihilation and finite-generator descent, then
   the existing quotient annihilation and iterated-quotient lemmas. Removed the
   redundant proof imports WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
   and WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine; scratch copies
   compile without them. Tested removing QuasiCoherentCokernelImage, which produces
   an unknown-constant error for quasiCoherent_cokernel_image, so retained it.
   All repository-baseline proof_deps remain used; the earlier report's tensor/kernel
   pruning describes the previous attempted delivery, not deletions from this
   repository baseline. No module is pruned from the target closure. Checked
   dag/units/sk-thm-p1.json realized: this item realizes no unit statement or step,
   and neither that record nor the chapter/unit route changes.
5. PASS: only proof, proof_deps and proof_origin differ in the existing node. The
   proof_deps equal the union of the steps' uses. The steps describe the actual
   generator argument, affine cokernel sections and reused private lemmas. The
   signature in lean.statement matches the unchanged Lean theorem. No new node
   fields are required.

Second-reader changes: removed the two redundant proof imports named above and
recorded this independent reading. No proof body or mathematical statement changed.
The delivered accounting is one original hole closed, zero holes added, zero left;
no target-closure module pruning is claimed.
