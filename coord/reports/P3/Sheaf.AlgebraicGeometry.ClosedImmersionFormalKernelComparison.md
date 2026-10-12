## What changed

Proved `AlgebraicGeometry.closedImmersion_formalKernel_comparison` in
`Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelComparison` without changing its
signature or any public import. The shorter proof uses the existing termwise
closed-pushforward equivalence and formal-system pullback. Mathlib's whiskering and
restriction of adjunctions make closed formal pushforward a right adjoint. It therefore
preserves the given limiting kernel fork. The supplied square lifts to the full
subcategory, and Mathlib's kernel-fork uniqueness gives the required isomorphism.

Replaced the broad closed-immersion equivalence import with its termwise module;
added the proof-only `FormalSystemsPullback` import. The second reader removed
redundant direct imports of `Adjunction.Restrict`, `Adjunction.Whiskering`, and
`Limits.Preserves.Shapes.Kernels`; their declarations are already available. Updated the
existing theorem docstring and the node's proof, proof_deps, and proof_origin to match.
There are no new declarations, nodes, interface changes, or forced adaptations.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.closedImmersion_formalKernel_comparison`
(node `aux-closed-immersion-formal-kernel-comparison`). No sorry remains in the item,
and no hole is added elsewhere: this is a proof from existing declarations, not a
new decomposition. The repository source now contains proofs of the termwise equivalence, formal
pullback, and tensor-pullback adjunction. The compiled dependency audit nevertheless
shows `sorryAx` for both the termwise equivalence and formal pullback, so the
comparison is conditional on existing upstream holes being closed. This delivery
adds no holes and does not claim a target free of `sorryAx`.

The final sandbox module compiles with no errors or warnings using `lcompile.py`.
The delivery dry run runs the declaration/axiom checks and preflight; its output is
the final validation. The source module remains a `module` file, and all statement
and definition signatures and public imports remain identical.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
  (`lem-weil-pbc-closed-immersion-coherent-equivalence`): only its existing termwise
  conjunct is needed, imported directly instead.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
  (`lem-weil-pbc-coherent-formal-modules-affine`).
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`
  (`lem-weil-pbc-coherent-formal-modules-local-exactness`).

The affine-completion kernel identification and local gluing steps are replaced by
right-adjoint limit preservation. Static comparison of this item's old and new
project import closures on the current repository removes these 25 modules
and their recorded nodes:

- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`: `lem-weil-pbc-tower-limit-exact-surjective-kernels`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`: `lem-weil-pbc-closed-immersion-coherent-equivalence`.
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceCompletion`: `lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal`: `lem-weil-pbc-coherent-formal-modules-isomorphism-local`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel`: `lem-weil-pbc-coherent-formal-module-kernel`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`: `lem-weil-pbc-coherent-formal-modules-abelian`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`: `lem-weil-pbc-coherent-formal-modules-affine`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineComplete`: `lem-weil-pbc-coherent-formal-modules-affine-complete`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineLimit`: `lem-weil-pbc-coherent-formal-modules-affine-limit`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient`: `lem-weil-pbc-coherent-formal-modules-affine-quotient`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstruction`: `lem-weil-pbc-coherent-formal-modules-affine-reconstruction`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesBinaryProducts`: `lem-weil-pbc-coherent-formal-finite-products-binary-products`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImage`: `lem-weil-pbc-coherent-formal-coimage-image`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine`: `lem-weil-pbc-coherent-formal-coimage-image-affine`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical`: `lem-weil-pbc-coherent-formal-cokernel-canonical`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelClosure`: `lem-weil-pbc-coherent-formal-cokernel-closure`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesEmptyProducts`: `lem-weil-pbc-coherent-formal-finite-products-empty-products`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesFiniteProducts`: `lem-weil-pbc-coherent-formal-finite-products`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoInvariant`: `lem-weil-pbc-coherent-formal-iso-invariant`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`: `lem-weil-pbc-coherent-formal-modules-local-exactness`.
- `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`: `lem-weil-pbc-coherent-module-local-on-open-cover`.
- `Sheaf.RingTheory.AdicCompletionNoetherian`: `lem-weil-pbc-adic-completion-noetherian`.
- `Sheaf.RingTheory.FiniteModuleComplete`: `lem-weil-pbc-finite-module-complete-over-complete-noetherian`.
- `Sheaf.RingTheory.NakayamaNilpotent`: `lem-weil-pbc-nakayama-nilpotent`.
- `Sheaf.RingTheory.PowerSeriesOntoCompletion`: `lem-weil-pbc-power-series-onto-completion`.

These are removals from this item's import closure. Other targets or modules may
still need them; no claim of global unreachability is made. Every node realizing
`sk-thm-p1`'s statement or proof steps is retained: the item and removed auxiliary
nodes are below those realized unit nodes.

## Where the brief, the DAG or earlier work was wrong

The original affine/local-exactness route was mathematically viable but unnecessary.
The available formal pullback theorem states exactly the equality of underlying
functors needed to restrict the module adjunction, and the termwise closed-pushforward
equivalence provides the other comparison. This proves preservation of categorical
formal kernels without any termwise-kernel assertion or annihilation hypothesis.
The E and P witnesses are used only with their specified underlying-system
comparisons; no arbitrary object is chosen from an unproved mere-existence theorem.

The local literature checkout lacks `literature/stacks-project/coherent.tex`.
The source statements were checked read-only against the official Stacks pages
[Tag 087T](https://stacks.math.columbia.edu/tag/087T) and
[Tag 0887](https://stacks.math.columbia.edu/tag/0887), and against the existing
termwise-equivalence and formal-pullback node records. No statement dispute was found.

## Second reading by P3

1. **Visible interface: PASS.** Diffed the sole delivered Lean module against the
   repository. The entire existing theorem signature is byte-for-byte identical,
   including both Noetherian hypotheses, the closed immersion, the chosen Abelian
   structure on X, both system isomorphisms, the commuting-square equation, and the
   supplied limiting fork on Z. The conclusion remains only a nonempty underlying
   inverse-system isomorphism. All four public imports are unchanged. The sandbox
   has no other delivered module, new declaration, definition, or change record.

2. **Proof and axioms: PASS with existing upstream holes.** Compiled the module
   using lcompile.py without errors or warnings. A scratch-copy #print axioms for
   closedImmersion_formalKernel_comparison lists propext, Classical.choice,
   Quot.sound, and sorryAx, and no others. Both existing termwise-equivalence and
   formal-pullback declarations also list sorryAx in the compiled library. The
   delivered text contains no sorry or forbidden declaration mechanism. P is
   specified on objects and morphisms by hP after a fully faithful inclusion;
   R is specified up to natural isomorphism by theta. The chosen adjunction is
   universal-property data. No arbitrary witness of a mere existence statement
   supplies an unconstrained object in a definition.

3. **Split statements: PASS, none.** No new statement or hole is split off.
   Read the existing termwise equivalence and formal pullback statements, the
   coherent-formal-system definitions, and the tensor adjunction. Checked the
   underlying constructions against [087T](https://stacks.math.columbia.edu/tag/087T),
   [088A](https://stacks.math.columbia.edu/tag/088A), and
   [0887](https://stacks.math.columbia.edu/tag/0887). The closed immersion and
   Noetherian hypotheses support the termwise equivalence; both Noetherian schemes
   support formal pullback; no flatness is needed for the adjunction. The proof
   applies to zero maps, zero systems, identity and empty closed immersions, and
   Q = 0 or the unit ideal without cancellation of a scalar or an extra hypothesis.
   It never claims that level evaluation preserves kernels.

4. **Route and pruning: PASS after import/report repair.** Read Mathlib
   Adjunction.restrictFullyFaithful, KernelFork.mapIsLimit, and
   KernelFork.mapIsoOfIsLimit. The directions of hP and theta give P left adjoint
   to R. Right-adjoint limit preservation and preservation of zero morphisms
   supply exactly the limiting mapped fork. Cancelling theta at D and its
   naturality at alpha give the required arrow square; hw.symm has the direction
   Arrow.isoMk expects. Kernel-fork uniqueness then gives precisely the conclusion.
   Searched lean/Sheaf and lean/WeilConjectures for formal-kernel comparisons and
   restricted adjunctions; no shorter ready-made formal comparison was found.
   Removal tests show both project proof imports are necessary. All three direct
   Mathlib proof imports can be removed together because existing imports expose
   their lemmas. Recomputed the import-closure pruning list against current source:
   25 modules, not the earlier 29. Every old proof_deps node absent from the new
   proof is listed under No longer needed. No removed node realizes a statement
   or step in dag/units/sk-thm-p1.json; its route is preserved.

5. **DAG alignment: PASS.** JSON comparison finds only proof, proof_deps, and
   proof_origin changed in the existing node. The node statement, Lean statement
   record, and all other fields remain unchanged. The three proof steps track E
   and theta, P and the tensor adjunction, then transport and uniqueness. The
   proof_deps union is exactly the existing termwise-equivalence, formal-pullback,
   and module-pullback nodes. The latter's Lean record includes the actual
   nonempty_tensorPullbackAdjunction used here. No new node requires validation.

Second-reading changes: removed three redundant Mathlib proof imports; corrected
upstream-proof wording and refreshed the pruning list to 25 current modules;
added this independent review. The proof body and signature were retained.
