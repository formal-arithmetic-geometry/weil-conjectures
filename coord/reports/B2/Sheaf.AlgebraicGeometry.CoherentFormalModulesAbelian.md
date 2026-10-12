## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian` by a
compiling reduction with its original theorem signature and public imports unchanged.
The proof inherits preadditivity, obtains finite products from ambient product closure,
extracts a limiting kernel fork from the existing `coherentFormalModule_kernel`, and
obtains cokernels from Mathlib's full-subcategory cokernel-closure machinery. It applies
`Abelian.ofCoimageImageComparisonIsIso`. For the termwise clause it chooses the canonical
cokernel cofork and proves that inclusion followed by every evaluation preserves its
colimit. This last categorical argument is proved in Lean, rather than split off.

Three new statement modules isolate the remaining geometric steps: finite-product
closure, ambient cokernel closure, and invertibility of the coimage-image comparison.
Each has one public theorem, a source, a complete proof in words, and a matching node.
Updated the original node's proof, proof dependencies, and proof origin to the actual
assembly. No definitions, existing theorem signatures, target signatures, or visibility
changed; no adaptations or change records are needed.

Read Stacks Tag 087X, label `lemma-inverse-systems-abelian`, including claims (a)--(d)
and the final coimage-image paragraph, at https://stacks.math.columbia.edu/tag/087X.
The local `literature/stacks-project/coherent.tex` named by the original node is absent
on this machine; the official Stacks page supplied the source. The original ten-step
node supplies the expanded additive and cokernel details omitted by Stacks. Checked the
unit `sk-thm-p1` and its realized fields: this item is below its realized unit statements
and steps, and the unit route is retained.

The prescribed LeanFinder, Loogle, and Mathlib grep searches found the abstract abelian
criterion and ObjectProperty machinery, but no coherent-formal-system specialization.
The later combined LeanSearch query returned HTTP Internal Server Error; this is recorded
as unavailable, not as a negative search. Searches are in `searches.jsonl`. Blueprint
searches for coherent formal systems, finite products, coimage and cokernels found no
existing blueprint statement for the three new geometric interfaces. A further library
search found the existing stabilized-kernel theorem and eliminated a proposed duplicate
kernel helper before delivery.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.coherentFormalModule_abelian`
(node `lem-weil-pbc-coherent-formal-modules-abelian`). The assigned module now contains
no `sorry`. This is a decomposition, not a proof independent of postponed geometry:
one original hole closed and three new holes added, for a delivery net of minus two.
The existing `AlgebraicGeometry.coherentFormalModule_kernel` also remains a dependency;
its hole is unchanged and was not added by this delivery.

Every hole added by this delivery:

- `AlgebraicGeometry.coherentFormalModules_closedUnderFiniteProducts`, in
  `Sheaf.AlgebraicGeometry.CoherentFormalModulesFiniteProducts`, node
  `lem-weil-pbc-coherent-formal-finite-products`.
- `AlgebraicGeometry.coherentFormalModules_closedUnderCokernels`, in
  `Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelClosure`, node
  `lem-weil-pbc-coherent-formal-cokernel-closure`.
- `AlgebraicGeometry.coherentFormalModules_coimageImage_isIso`, in
  `Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImage`, node
  `lem-weil-pbc-coherent-formal-coimage-image`.

Each is strictly part of the original argument: respectively step 2, the object-condition
part of step 3, and steps 8--9. None states abelianness or the assigned conjunction. Kernel
existence and the formal categorical cokernel/evaluation argument are written in Lean.
No arbitrary object is extracted from an unproved mere-existence statement: the kernel
and its universal factorization are determined by their universal property, and the
cokernel is Mathlib's canonical universal construction.

Validation: all four delivery modules compile in import order through `lcompile.py --all`,
without compiler errors or warnings. The prescribed `deliver3.py --no-push` printed OK:
compilation and preflight pass, with only the second reading left for the next worker;
nothing was pushed. The exact original theorem signature and the 100-character Lean line
limit were checked separately. Edge cases checked mathematically: empty finite
products and the empty scheme, zero systems and zero arrows, and the ideals zero and the
unit ideal. For I=0 the systems are constant up to their specified transition isomorphisms;
for the unit ideal all terms are zero. The cokernel closure concerns ambient cokernels;
the kernel construction deliberately does not claim termwise injectivity. The comparison
statement quantifies over arbitrary kernel/cokernel structures; universal-property
uniqueness makes its truth independent of those choices.

## No longer needed

Removed these six direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

They are replaced there by the existing kernel theorem and the three geometric interfaces.
These modules and their original proof nodes remain needed below the kernel theorem or in
the three new nodes' proof plans. Thus no module is claimed pruned from the target closure,
and no original geometric lemma is claimed unnecessary globally. The original direct
Artin-Rees and affine-preliminary proof steps now belong to the existing kernel node and
the comparison node; their mathematical work is retained. No unit-level node is bypassed.
The proposed new kernel-existence module was deleted and is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The assigned node's direct proof plan omits the already stated, stronger
`lem-weil-pbc-coherent-formal-module-kernel`. Its unique-factorization clause immediately
supplies the kernels needed by the abelian criterion, avoiding a duplicate construction.
The original geometric dependencies state affine calculations but not the global closure
and comparison interfaces; the three new statements record those remaining steps rather
than using those dependencies as though they already asserted global abelianness.

Stacks' displayed calculation contains `a^{-1}(I^l N)` where `f^{-1}(I^l N)` is meant;
the original node had already identified this typo. No disputed statement or interface
repair was needed.

A traversal of the whole reachable statement/proof DAG encountered an inherited cycle
at `lem-weil-pbc-sheaf-algebraic-structures-objects`. A separate reachability check for
each of the four delivered nodes confirmed that none reaches itself: this delivery
introduces no cycle involving its nodes. This unrelated baseline issue is reported here
for the maintainer; its nodes were not changed.

## New nodes

`lem-weil-pbc-coherent-formal-finite-products` records closure of the defining object
property under ambient finite products, including the empty product. Its proof is the
termwise direct-sum argument with ideal products and quotients checked on affine sections.
It is stated in `lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesFiniteProducts.lean`.

`lem-weil-pbc-coherent-formal-cokernel-closure` records that the vertex of every ambient
cokernel cofork of coherent formal systems satisfies the same object conditions. It does
not assume the formal category is abelian and does not assert the whole assigned cokernel
universal-property clause. The assigned module proves that clause by Mathlib's creation
and preservation machinery. It is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesCokernelClosure.lean`.

`lem-weil-pbc-coherent-formal-coimage-image` records invertibility of the canonical
comparison, under arbitrary kernel and cokernel structures. Its proof uses restriction,
the stabilized-kernel construction and the affine finite-module equivalence, then the
module first isomorphism theorem and locality. It is stated in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesCoimageImage.lean`.

## Second reading by B2

1. **Comparison with the repository.** I diffed the assigned module against the repository copy. The theorem signature, definitions, visibility, and existing declarations are byte-for-byte unchanged; only the proof body, proof-only imports, and explanatory docstring changed. The three added modules and their node files are explicitly listed above.

2. **Compilation and proof hygiene.** I compiled all four delivered modules with `lcompile.py --all`; they compile without errors or warnings. The assigned theorem has no `sorry`, and each remaining `sorry` is exactly one named public theorem listed above with a matching node and a complete source-based proof docstring. No definition contains `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was added. The three split-off holes are a deliberate decomposition of the original geometric argument, not a weakened restatement.

3. **Statement review.** I checked each new statement against its Lean type and its edge cases (empty products, zero arrows and systems, the zero and unit ideals, and the empty scheme). Finite-product closure, ambient cokernel closure, and invertibility of the coimage-image comparison are each strictly smaller than the assigned abelianness statement and are exactly the interfaces consumed by the proof. Their docstrings state the intended constructions and sources; no arbitrary witness is used as data.

4. **Proof route and pruning.** The proof uses the existing stabilized-kernel theorem, the three new geometric interfaces, and Mathlib's full-subcategory and coimage-image machinery. I checked that removed imports are proof-only imports no longer referenced by the assigned proof and are documented under `## No longer needed`; no unit-level route is bypassed. The node proof and `proof_deps` lists follow the actual declarations used.

5. **DAG and unit consistency.** I inspected all four changed node files. Each new node has source, proof steps, proof dependencies, searches, Lean record, chapter, unit, and split status; the assigned node records the revised assembly. The `sk-thm-p1` unit route and realized unit steps remain respected. The prescribed dry-run delivery check now passes its static review requirements.

No additional changes were necessary in this second reading.
