## What changed

Proved `AlgebraicGeometry.Scheme.Modules.ideal_tensor_multiplication_kernel_control`
with its signature and all existing public imports unchanged. Added proof-only imports for
coherence/finite affine sections, affine finite-type descent, tensor sections, qcqs pushforward,
affine image sections, quasi-coherent kernels/cokernels, and finite tensor products.
Updated the existing node's proof, proof_deps, and proof_origin to match the implemented route.

Finite affine sections of the ideal follow from its injective section inclusion into the
Noetherian section ring. Tensor sections are finite by Mathlib and the affine tensor comparison;
the affine finite-type criterion and Noetherian coherence criterion give source coherence.
Quasi-coherent kernel closure gives the second clause directly. The private balancing helper,
tensor induction, and injectivity of the kernel section inclusion prove annihilation by I(U)^n.
Fully proved private helpers compute recursive-power affine ranges using the affine image
formula and prove quasi-coherence. Multiplication by that recursive power vanishes on the affine
basis, hence globally by sheaf separatedness; its image is zero by epi/mono cancellation.

All private helpers are proved, not split-off obligations. Their range/power arguments are
adapted from the already proved private helpers in IdealTimesQuasiCoherentAffineSections;
the ideal quasi-coherence helper uses the independent qcqs pushforward theorem to avoid its
current import cycle. No new public interface, definition, axiom or module was introduced.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Modules.ideal_tensor_multiplication_kernel_control`
(node `lem-pc-ideal-tensor-multiplication-kernel-control`). Added 0 holes. No sorry remains in
the delivered module. This is a proof, not a decomposition. The full module compiles without
warnings within the unchanged 60-second single-file limit (about 41 seconds locally).
The final route is independently checked by a scratch copy with `#print axioms` for the
main theorem and every private helper, and by the delivery axiom probe.

Edge cases: n=0 uses the identity recursive-power inclusion and the unit ideal's full range;
the same balancing equation forces the multiplication kernel to vanish. Zero/unit ideals and
the zero module need no excluded case. The affine basis argument handles the empty scheme
without choosing a point or assuming a nonempty cover.

## No longer needed

No original import was removed: all four public imports are required by the unchanged statement.
The planned proof dependency `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` and module
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian` are not needed: the conclusion
asks only quasi-coherence of the kernel, supplied directly by the source library's kernel theorem.
The planned dependency `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` and module
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` are not imported;
the needed private calculations are proved here from independent tensor/image interfaces.
The trial proof import `Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover` and node
`lem-weil-pbc-ideal-power-product-zero-affine-cover` were also removed from the final route;
affine vanishing and global sheaf separatedness prove the zero image directly.
These are dependencies pruned from this item; no claim is made that other target branches do
not still require them. The required blueprint unit route is retained.
The second reading also removed the redundant proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`: it is publicly re-exported
by the directly used QuasicoherentCokernel module. Its kernel theorem and DAG dependency
remain used; this import cleanup does not claim that its module leaves the target closure.

## Where the brief, the DAG or earlier work was wrong

The planned ideal-times import cannot be added against the current source graph: it reaches
this item through Modules.ClosedImmersion -> Cohomology.DirectImage ->
Cohomology.DirectImage.FiniteFreeComplex -> IntegralIdealProperCohomology ->
IntegralIdealComparisonFiltrations -> IntegralIdealCommonSubmodule -> RankOneGenericIdealInclusion
-> GenericIdealStalkEmbeddingExtension -> LocalClosedIdealMapExtension ->
ClosedStructureAmbientIdealExtension -> IdealPowerTensorImageLift -> this item.
The affine-zero criterion also reaches that cycle through the ideal-times module.
The cached compiled library initially accepted those imports, but the source import-direction
check exposed the issue. Both were removed; every final proof-only library import was checked
not to reach this item. No dependency module was edited or adapted.

The DAG's coherent-kernel step proves more than the second conclusion needs and is pruned.
The original signature is true and unchanged. The source was read at Stacks Tag 01YB
(https://stacks.math.columbia.edu/tag/01YB), including its omitted kernel-annihilation argument.
Searches: LeanFinder found algebraic tensor-kernel ingredients, Loogle found tensor exactness
lemmas, and the logged grep plus source-library searches found no direct full sheaf theorem.
The Lean proof supplies the omitted balancing argument explicitly.

## Second reading by R2

1. Compared the entire delivered module with the repository version by `diff` and checked
   the existing theorem signature as an exact string, including its local monoidal instance,
   all hypotheses and all three conclusions. The four public imports and existing docstring
   are unchanged. There are no definition changes, public additions, change records or forced
   adaptations. Restored the original single space before `:= by`. Verdict: interface preserved.
2. Independently compiled the original delivery without warnings in 42.8 seconds. Scanned
   the final source for sorry, axiom, unsafe, opaque, extern, implemented_by and kernel-check
   bypasses: none. The ideal-quasi-coherence helper is a kernel of the actual structure map;
   its pushforward hypothesis is supplied by the closed immersion's qcqs instances. The
   product helper identifies categorical and abelian images. Tensor induction computes the
   affine ranges, and the recursive-power induction uses range of a composite, mapped ideal
   products, and `pow_succ'`. The balancing helper uses injectivity and ring commutativity;
   the main proof constructs the linear map h mapped to a tensor h, proves r z=L(mu(z)),
   then uses the kernel condition and injectivity. It does not choose any data from an
   unproved existence theorem. Checked `#print axioms` for the target and all seven private
   helpers in an independent scratch copy after the import cleanup: it compiled without
   warnings in 37.9 seconds and all eight declarations use only propext, Classical.choice
   and Quot.sound. Verdict: a genuine proof.
3. No statements were split off and no new nodes were added. Read Stacks Tag 01YB at
   https://stacks.math.columbia.edu/tag/01YB, specifically its second short exact sequence
   and omitted assertion that the ideal power kills the kernel. Its kernel of the map to
   the product is the same as the kernel of multiplication into H, since the image inclusion
   is monic. No hypothesis on the quasi-coherent F from the larger lemma is needed for this
   intermediate assertion. Tested n=0 (the unit ideal and full range), zero and unit ideals,
   the zero module, and the empty scheme: the argument excludes none. All private helper
   statements are proved. Verdict: no new obligations or disguised restatement.
4. Independently searched LeanFinder for “An ideal annihilates the kernel of its tensor
   multiplication map into a module” and searched lean/Sheaf, lean/WeilConjectures and
   Mathlib ideal/tensor sources for kernel, multiplication and power-range formulations.
   The returned algebraic quotient/flatness lemmas do not supply the sheaf statement.
   Existing affine power calculations occur in the reported ideal-times module or private
   helpers; importing the former would create the reported source cycle. The direct tensor
   balancing route remains appropriate. Checked each added import against its use; removed
   only the redundant direct kernel import, whose declarations are publicly re-exported by
   QuasicoherentCokernel. Both unused original proof-dependency nodes (coherent kernel and
   ideal-times affine sections) are listed under No longer needed. Read
   dag/units/sk-thm-picard-coherence.json: its realized statement/step lists are empty, and
   this local calculation remains in the coherent higher-image/ideal-devissage route.
   Verdict: pruning complete for this item's old proof dependencies; unit route preserved.
5. Compared old/new node JSON field by field: changes are confined to proof, proof_deps and
   proof_origin; statement, stmt_deps, lean signature, source, unit and blueprint are unchanged.
   The union of the five steps' uses is exactly proof_deps. Checked the imported statements:
   coherent/finite-type equivalence, finite coherent affine sections, affine-cover finite-type
   criterion, tensor quasi-coherence/bijective affine sections, qcqs pushforward, quasi-coherent
   kernels, and affine cokernel-image sections supply precisely the facts the proof takes.
   The elementary balancing step uses only injectivity, commutativity and bilinearity.
   Verdict: the node describes the Lean proof and no unit-level result is bypassed.

Second-reading changes: signature-separator whitespace restored; redundant proof-only kernel
import removed; independent review and precise import-pruning/axiom-check evidence added to
this report. No mathematical proof rewrite was necessary. Closed 1 of 1 original holes;
added 0 holes and split off 0 statements.
