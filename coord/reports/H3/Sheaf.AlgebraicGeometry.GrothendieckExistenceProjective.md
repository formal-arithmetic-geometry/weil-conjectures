## What changed

Replaced the proof of `AlgebraicGeometry.completion_isEquivalence_of_projective_embedding`
with a compiling reduction following Stacks [0885](https://stacks.math.columbia.edu/tag/0885).
The existing theorem signature, universes, visibility and docstring are unchanged.

The proof obtains full faithfulness from
`formalCompletion_map_bijective_of_proper`, constructs the ample module from
`projective_closedImmersion_ample_invertible`, and chooses one natural twist satisfying
both `coherentFormalModule_kernel_twist_vanishing` and
`exists_finite_generatingSections_tensorPow_of_isAmple`. The new lemma
`formalModule_cover_from_lifted_sections` produces a map whose first component is epi;
`coherentFormalModule_epi_iff_first_component` makes it a formal epimorphism.

A completely proved private categorical argument chooses a completed cover of each formal
module and of the kernel of that cover. It lifts their composite by full faithfulness,
identifies its cokernel with the original module, and uses preservation of cokernels to
obtain essential surjectivity. `formalCompletion_exact` supplies the abelian structures,
additivity and exactness; Mathlib's `Functor.exact_tfae` gives finite-colimit preservation.

Proved private helpers identify the quotient-Spec kernel ideal with the ofIdealTop ideal
used by the proper full-faithfulness and vanishing declarations, and transport exactness
between the unique zero-morphism structures. All new imports of the main module are
proof-only. The new module's public imports provide its statement types.

Both delivered modules compile without warnings using lcompile.py, in dependency order.
The categorical helper and the ideal-identification helper were also compiled separately
while developing the proof. The new and existing DAG records follow the actual proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.completion_isEquivalence_of_projective_embedding`
(node `lem-weil-pbc-grothendieck-existence-projective`). There are no sorries in its module.

Added one hole:
`AlgebraicGeometry.formalModule_cover_from_lifted_sections`
(node `lem-weil-pbc-formal-module-cover-from-lifted-sections`), in the new module
`Sheaf.AlgebraicGeometry.FormalModuleCoverFromLiftedSections`. Its proof is exactly
`:= by sorry`. Its docstring and node give the full compatible-section lifting,
tensor-dual map construction, quotient factorization and first-component epi argument.

This is a decomposition: one hole closed and one smaller hole added, net zero new-hole
progress before accounting for existing imported dependencies. It is not an unconditional
sorry-free proof of Grothendieck existence: the existing geometric and exactness lemmas
remain dependencies as intended by stage 3.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian` and removed its node
`lem-weil-pbc-coherent-formal-modules-abelian` from the item's direct proof dependencies.
The abelian witnesses needed here are already supplied by `formalCompletion_exact`.
That module still publicly imports CoherentFormalModulesAbelian, so no claim is made
that the latter module disappears from the targets' transitive import closure.

Every other original import is used. No other original proof-plan nodes or modules are
pruned. The new cover lemma replaces the gap in steps 5 and the construction part of 6;
the existing global-generation, vanishing and epi-detection declarations remain used.

## Where the brief, the DAG or earlier work was wrong

The DAG's steps 5–6 had no Lean declaration constructing the compatible lifted sections
and factoring their maps through the quotient completion. The existing vanishing lemma
and global-generation lemma supply the hypotheses, not the compatible formal map. The
new lemma isolates exactly that construction, rather than renaming essential surjectivity.

The proper full-faithfulness and vanishing statements use
`ofIdealTop (I.map ΓSpecIso.inv.hom)`, while this item uses the kernel of Spec(A/I) to Spec(A).
The private helper proves their equality; no interface or definition change is needed.

`formalCompletion_exact` returns arbitrary abelian structures as Nonempty witnesses,
while its additivity and exactness clauses use the original preadditive/zero structures.
These are unique, but not definitionally equal. The private transport helpers resolve
this issue without adapting any dependency or changing a signature.

The new statement was checked on d=0, the empty scheme, a zero formal system, and the
zero/unit ideal cases. It needs neither ampleness nor a complete base once vanishing
and the finite generating family are supplied. A unit ideal forces the formal terms
zero. For zero ideal the systems stabilize, so the claimed cover is consistent with
ordinary finite generation after the given twist. No data definition chooses an
arbitrary witness from an unproved existence theorem.

## New nodes

`lem-weil-pbc-formal-module-cover-from-lifted-sections` states the construction in the
first essential-surjectivity paragraph of Stacks 0885. It assumes a specified finite
family generating F_1 tensor L^d and H^1 vanishing of all twisted transition kernels;
it concludes only existence of a map from a completed coherent module whose first
component is epi. It does not assert algebraization, full faithfulness, exactness or
an equivalence. The parent proof combines it with the existing epi criterion and the
proved categorical cokernel argument. Blueprint searches for compatible global sections,
completion and quotient found no existing blueprint statement of this construction;
Mathlib and repository searches found no matching declaration. LeanSearch was unavailable
(HTTP 500), recorded as unavailable, not as a negative search result.

No change record is required: no existing signature, definition or public import changed.

Latest retry (2026-10-13): `lcompile.py --all` successfully compiled both delivered
modules in dependency order (cover lemma 3.4 seconds, main module 4.4 seconds), exit
code 0, with no warnings. The proof files remain unchanged.

The required `deliver3.py H3 Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective
--no-push` now passes the former Python import failure, but stops before compilation
with `FAILED: missing import source modules` for these existing Mathlib modules:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`
- `Mathlib.RingTheory.AdicCompletion.Basic`

All three source files exist in the installed Mathlib. The clone helper
`tools/import_cycles.py:source_roots` changes the supplied `/home/ubuntu/weil-lean`
root to `/home/ubuntu/weil-lean/lean` because the latter directory exists. It then
looks for packages under `lean/.lake/packages`, which does not exist. The actual
package directory is `/home/ubuntu/weil-lean/.lake/packages`, linked to the installed
source checkout's packages. Thus the source inventory fails independently of the
successful local compilation. No tools or package paths were changed or bypassed.
The initial dry run in this retry had not printed OK. No worker-side tooling repair
was made. A subsequent repeat succeeded, as recorded below.

Final verification (2026-10-13): the repeated required dry run printed
`OK (dry run): commit fa5f92c93c compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.` The source-root
failure above was transient and no longer blocks the delivery. Both Lean modules
and all delivery checks pass; the independent second reading remains to be written
by the second worker. This worker did not push or deliver.

## Second reading by H3

1. **Repository comparison.** I compared both delivered Lean modules and the existing DAG node with the repository versions. The existing target declaration and all pre-existing declaration signatures are unchanged byte for byte; the only additions are the proof, proof-only imports, and the separately declared split theorem and node.

2. **Compilation and proof hygiene.** `lcompile.py --all` compiles both modules successfully with no warnings. The target module contains no `sorry`; the sole remaining `sorry` is the named public theorem `AlgebraicGeometry.formalModule_cover_from_lifted_sections`, exactly as listed in the report and represented by its node. No forbidden declarations or hollow definitions occur. The target proof's categorical helpers are private and use only the permitted imported results.

3. **Statement and split review.** The target proves the unchanged `completion_isEquivalence_of_projective_embedding` statement. The split theorem is a strictly smaller construction: it supplies only a completed coherent cover with epi first component from finite generating sections and the stated cohomology vanishing. It does not restate essential surjectivity or equivalence. Its hypotheses and conclusion agree with the Lean declaration and its docstring records the intended section-lifting, tensor-dual, quotient-factorization argument. Repository and Mathlib searches reported no existing matching declaration.

4. **Pruning and route.** The proof uses the projective ample, vanishing, global-generation, formal-completion exactness/full-faithfulness, and epi-detection declarations in the route recorded by the node. The old direct abelian-category import and node are no longer directly needed and are removed from imports and `proof_deps`; the remaining imports are used. The unit route is retained: the new cover construction realizes the section-lifting portion, followed by the exact categorical cokernel argument.

5. **DAG consistency.** The target node's proof steps, `proof_deps`, and `proof_origin` match the Lean proof. The new split node has the required statement, source, proof steps, searches, Lean record, chapter, and unit metadata, and its Lean statement matches verbatim. No statement or definition change record is required.

I changed only this report section during second reading; no Lean proof or declaration needed repair.
