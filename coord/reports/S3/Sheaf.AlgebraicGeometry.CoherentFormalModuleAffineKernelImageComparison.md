## What changed

Proved `AlgebraicGeometry.coherentFormalModule_affine_kernel_image_comparison` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison`, with its
original signature, universes, visibility, and docstring unchanged.

The proof takes sections directly on the given affine open rather than transporting
formal systems to Spec. The existing proved
`coherentFormalModule_affine_open_sections_adic` computes finite-level annihilation
and successor transition kernels. The existing completed-scalar-limit
and finite-limit declarations supply finite completed modules and their projections.
The induced map of limits is proved completion-linear by checking every coordinate.
Restriction of scalars identifies the projection kernels with extended ideal powers.
The remaining private lemmas prove the kernel transition range formula, quotient-image
equality via equal fibers, and extension of mono section-range equality from U to all
smaller opens using basic-open denominators and sheaf separatedness.

Proof imports added: `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic`,
`Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit`,
`Sheaf.Algebra.Category.ModuleCat.AdicTowerFiniteLimit`, and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.
All added proof imports are non-public; no `import all` remains.

Updated `new-formal-affine-kernel-image-comparison` proof, proof_deps, and proof_origin
to match this route. No existing interface or other module was adapted. The node is
below unit level and is absent from `sk-thm-p1.realized`; that unit's route is preserved.

Validation: repeated single-file compilation through lcompile.py, including the
combined final file; no compiler warnings. Checked zero local sorry occurrences and
100-character line limits. The argument also covers empty U/W, zero and unit ideals,
zero modules/maps, and equal indices: it introduces no nonemptiness, proper-ideal, or
strict-index hypotheses. The completion data are determined by limit universal
properties and the coordinate scalar equation; the map f is explicitly the conjugated
map of limits, not an arbitrary existence witness used in a definition.

Searches: LeanFinder on equality of affine quasi-coherent submodules found ideal-sheaf
extensionality results but no direct comparison; Loogle on Submodule.mkQ found the
quotient kernel tools; grep/rg found range_map_kernelι, the basic-open denominator
lemma, and the existing completed-scalar and finite-limit declarations. Read their
Lean signatures and proofs. The cited local coherent.tex is absent on this machine;
read the official Stacks 087W and 087X pages instead.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.coherentFormalModule_affine_kernel_image_comparison`
(node `new-formal-affine-kernel-image-comparison`).

All six remaining private helper theorems are proved. No sorry remains in the item, and no
sorry, new public statement, or new module is added. This is one hole closed and zero
holes added, not a decomposition. Existing dependencies may retain their own holes;
this delivery proves the item from the existing named library declarations.

## No longer needed

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.Modules.Tilde` (direct tilde-equivalence step).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
  (`lem-weil-pbc-coherent-formal-modules-affine`).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects`
  (`lem-weil-pbc-coherent-formal-modules-restriction-objects`).

Removed the corresponding direct node dependencies, including
`lem-weil-pbc-affine-tilde-gamma-adjunction`. The affine equivalence, its inverse/reconstruction,
and formal-object restriction are unnecessary for this proof. The tilde adjunction
can still occur transitively through the existing basic-open localization and
quasi-coherent section theorems; no global unreachability is claimed.
The direct ideal-product dependency and its import are also removed after the second
reading: the existing affine-open adic-sections theorem supplies that entire step.
The quasi-coherent image/cokernel and quasi-coherent kernel dependencies remain needed. Every retained explicit proof import supplies declarations used in the proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature mismatch was found. The DAG's Spec-transport/equivalence
route was longer than necessary: direct sections on U already satisfy the algebraic
adic-tower hypotheses. Likewise the final subsheaf comparison can be proved by
basic-open denominators, cokernel vanishing and sheaf separatedness without a separate
formal restriction or tilde-transport theorem. The updated DAG records these changes.

## Second reading by S3

1. Compared the only delivered module with the repository using diff and the declaration
   parser. The original public theorem signature, universes, visibility, docstring and
   all public imports are unchanged. No definitions or other interfaces change. PASS.
2. Read the full proof and all six remaining private helpers. Local compilation and a
   scratch-copy `#print axioms` check succeed. The target uses only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from existing open dependencies.
   There is no local sorry, forbidden declaration, hollow definition or arbitrary
   existence witness: the modules are specified by limit comparisons and the residue
   scalar equations, and f is explicitly the conjugated limit map. PASS.
3. No statements are split off and no new holes or modules are added. Checked empty
   opens, zero/unit ideals, zero maps and l=k=m: the arguments use only the written
   non-strict index inequalities; sheaf separatedness handles the empty cover and
   all quotient/kernel calculations retain these degenerate cases. PASS.
4. Repeated local searches for affine section vanishing, subsheaf range equality and
   completed projections, and a LeanFinder query with different wording. Mathlib
   search returned structure-sheaf localization facts rather than this module-valued
   comparison. Found the already proved affine-open adic-sections theorem, removed
   the duplicate private sections_adic proof, and used that public theorem instead.
   Removed both import-all dependencies; remaining proof imports supply the actual
   tools used. The original three removed node dependencies are all listed above.
   The item is absent from sk-thm-p1.realized and no unit step is bypassed. PASS.
5. Compared node JSON: only proof, proof_deps and proof_origin change; the statement
   and Lean signature records agree with the unchanged theorem. Updated step 1 to
   cite the existing affine-open adic-sections node and moved the coherence criterion
   citation to the final step where it is still used. proof_deps is exactly the union
   of step uses. No new node is required. PASS.

Changed the duplicate helper to a use of
`AlgebraicGeometry.coherentFormalModule_affine_open_sections_adic`, pruned its two
private-access imports, and synchronized the node and report. The repaired scratch
axiom check compiles in 11.3 seconds.
