## What changed

Added a categorical reduction of `preservesCokernels_etaleTensorSectionsFunctor`. The proof uses two new intermediate modules: local surjectivity of tensor-section maps and exactness at the middle term of the tensor-section cokernel sequence. The final proof constructs the mapped cokernel using `ShortComplex.Exact.gIsCokernel`, transports it through `CokernelCofork.isColimitMapCoconeEquiv`, and applies `Functor.preservesCoequalizers_of_preservesCokernels`. Added proof-only imports for local-surjectivity under sheafification, the abelian structure on additive groups, the coequalizer API, and the two new intermediate modules. Existing signatures and public imports are unchanged. All three delivery modules compile without warnings under lcompile.py; deliver3.py --no-push printed OK. No files are pushed.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.Modules.preservesCokernels_etaleTensorSectionsFunctor`, by a complete compiling proof from two strictly smaller intermediate declarations. This is a decomposition, not a proof free of new holes: one hole closed, two holes added, net minus one before any closure effects. No sorry remains in the item module. The new declarations `etaleTensorSections_locallySurjective` and `etaleTensorSections_cokernel_exact` remain `sorry`, with nodes `lem-sc-etale-tensor-sections-local-surjectivity` and `lem-sc-etale-tensor-sections-cokernel-exact`.

## No longer needed

None. The existing naturality and tensor-section sheaf imports remain used. All four original proof dependencies remain: the adjunction is used by the unchanged additive instance, and the specified quasi-coherent tensor sheaf by the unchanged object comparison. The two new intermediate modules add no replacement for these dependencies.

## Where the brief, the DAG or earlier work was wrong

Step 2 of the original plan contains both local lifting of arbitrary cokernel sections and local lifting of sections annihilated by the cokernel projection. Neither interface was separately stated. They are now the two new nodes, with source [Stacks 070S(2)](https://stacks.math.columbia.edu/tag/070S) and [03FH(1)](https://stacks.math.columbia.edu/tag/03FH). The unit route is retained. LeanSearch returned an Internal Server Error; Loogle, LeanFinder and source searches supplied the generic categorical tools, but no exact tensor-section theorem. No target statement was changed.

## New nodes

`lem-sc-etale-tensor-sections-local-surjectivity` is stated in `EtaleTensorSectionsLocalSurjectivity.lean`.

`lem-sc-etale-tensor-sections-cokernel-exact` is stated in `EtaleTensorSectionsCokernelExact.lean`.

## Second reading by F2

1. Interface comparison: read the full repository/sandbox diff. The only Lean changes to
   the existing module are five plain (proof-only) imports and the final theorem body.
   Every existing declaration signature, definition body, visibility, and public import
   is byte-for-byte unchanged. There is no statement change or forced adaptation.
2. Proof and axioms: independently compiled all three modules through lcompile.py --all;
   all compile without warnings. The final proof obtains an epi using local surjectivity,
   combines this with middle exactness via ShortComplex.Exact.gIsCokernel, transports
   the cofork's universal property, and uses additivity to preserve coequalizers.
   Scratch #print axioms checks on the final theorem and both new theorems report only
   propext, Classical.choice, Quot.sound, and sorryAx. The two named split theorems are
   the only new holes; no forbidden declarations or data chosen from new unproved
   existence assertions occur. The original constructions were not changed.
3. Split statements: read Stacks 070S(2), 03FH(1), and 0096, and the existing
   RingedSpace.module_exactness_local_lifting and sheafified_cokernel_local_image
   interfaces. Local surjectivity assumes an epi and concludes covering image sieves;
   middle exactness assumes a specified cokernel sequence and concludes only equality
   of image and kernel. Both require the actual tensor maps componentwise, so neither
   silently assumes arbitrary natural transformations are pullback maps. They isolate
   different parts of the original argument, rather than restating coequalizer
   preservation. Both statements have complete docstring arguments and matching nodes.
   Checked the zero morphism (middle kernel is zero when the cokernel map is identity),
   an epi (middle exactness requires local lifts of every section), zero modules, and
   the empty scheme (the empty cover supplies local criteria). No flatness is used:
   preservation of cokernels, not preservation of kernels, supplies the pulled-back
   exact sequence. Canonical open restriction comparisons match the units and hence
   the normalized composition maps. The remaining work is formalizing these local
   comparisons, not another categorical cokernel argument. Independent LeanFinder
   and Loogle searches, plus rg on the library and Mathlib, found generic sheaf and
   epi APIs but no theorem for these normalized tensor-section restrictions. Neither
   split theorem closes in a few minutes from those APIs alone.
4. Route and pruning: inspected sk-prop-h2.json (its realized statement and step lists
   are empty), the original proof plan, and the new categorical proof. The construction
   still realizes the additive comparison's tensor-cokernel step; no unit is bypassed.
   The five added imports supply the two actual split lemmas, sheafification local
   surjectivity, abelian-group instances, and the additive coequalizer API. Removing
   Grp.Abelian experimentally fails additivity and Balanced instance synthesis, so it
   stays proof-only. No old dependency is pruned: the original adjunction and tensor
   sheaf remain used in the unchanged declarations. Corrected the DAG and the report
   to record this, rather than dropping those dependencies from proof_deps.
5. Node agreement: checked each new lean.statement verbatim against its declaration,
   the scheme universe, absence of quasi-coherence hypotheses, the component equalities,
   and the middle-exactness witness. Parent proof steps accurately name the two new
   declarations and the Mathlib assembly. Restored the two original dependencies used
   by the unchanged declarations, added the intermediate ancestor to both new nodes'
   blueprint.from.via paths, and recorded the independent searches. No existing node
   fields outside proof, proof_deps, and proof_origin were changed.

Second-reading changes: repaired dependency accounting and blueprint provenance, added
independent search evidence, and clarified the report. The compiling Lean proof was kept.
This delivery is a decomposition: one original hole closed, two strictly smaller holes
added; it is not a fully proved module or positive net sorry reduction.
