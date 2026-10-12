## What changed

The existing theorem `CategoryTheory.DecreasingFiltration.filteredComplex_quotient_image_comparison`
now has a complete Lean proof from one deferred kernel calculation. Its signature is unchanged.
The proof constructs the quotient-complex map with `cokernel.desc`, proves its projection square,
and assembles the required image isomorphism from two epimorphisms with equal kernel subobjects.
The final representative equation follows from the descent equation, not from an arbitrary choice
of an isomorphism.

Added `Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis`, fully proved. The four helper calculations that duplicated private declarations in `FilteredComplexFirstPageCyclesBoundaries` are now local proof terms at their call sites, so the delivered module introduces no duplicate theorem declarations. Evaluation of the
quotient sequence gives its degreewise epimorphisms and kernels. Inverse-image calculations identify
the cycle representative subobject with the pullback of the quotient cycles. Pullback stability of
epimorphisms gives the map to cycles. A separate image-and-sum calculation identifies the image of
the graded projection with the filtered cycle subobject and gives the other epimorphism. This lemma
needs only `p ≤ p+r`, not `1 ≤ r`.

Added `Sheaf.Algebra.Homology.FilteredComplexRepresentativeKernels`, stating only the equality of
the two kernel subobjects on representatives. It assumes the projection equations for arbitrary
maps; it does not assert an image isomorphism or construct the quotient map. Its source and complete
refinement argument are in its docstring and node.

All three modules compile together using `lcompile.py --all`. No signatures, definitions, public
imports, instances or visibility of existing declarations were changed. New modules use proof-only
imports of the existing subobject calculus. The original node now records the actual reduction.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.DecreasingFiltration.filteredComplex_quotient_image_comparison`
(node `lem-sp-filtered-complex-quotient-image-comparison`). This is a decomposition, not an
axiom-free proof of the entire comparison: it depends on the new kernel theorem below.

Also proved `CategoryTheory.DecreasingFiltration.filteredComplex_representative_epis`
(node `lem-sp-filtered-complex-representative-epis`) without any local hole, including both
representative equations and epimorphism assertions.

Added exactly one hole, and this is every `sorry` left in the delivery:
`CategoryTheory.DecreasingFiltration.filteredComplex_representative_kernels`
(node `lem-sp-filtered-complex-representative-kernels`). Its proof is exactly `by sorry` in its
own new module. No hole remains inside the original theorem, any definition, or any private helper.
Thus the original hole is reduced to one strictly smaller kernel calculation; net holes closed
minus added is zero.

## No longer needed

Removed the original proof-only import `Sheaf.CategoryTheory.Filtration` from the comparison
module. Its definitions are already publicly supplied through `FilteredComplexSubquotients`.
This does not make the filtration node or module globally unnecessary.
Also removed the unused trial import
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject` from the new representative module;
its proof uses only the existing subobject-limits extension and Mathlib. The four duplicate
private helper declarations (`exists_image`, `pullback_inf`, `pullback_kernel_of_eq`, and
`step_mono`) were pruned and replaced by local proofs at their use sites.

No planned mathematical dependency node is pruned: the abelian-category, filtration and
subquotient definitions are all used. No unit statement or unit step is bypassed. No additional
spectral-sequence, convergence, finite-filtration or first-page comparison lemma is imported.

## Where the brief, the DAG or earlier work was wrong

The original node had only definition dependencies for a multi-step categorical argument. The
representative epimorphism and kernel calculations were not available as stated declarations.
The new nodes expose those parts; the former is now actually proved. The main proof follows the
original cycle-boundary route rather than using a downstream spectral-sequence theorem.

The source file `literature/stacks-project/homology.tex` is absent in this checkout. The public
Stacks Tag 012K webpage was inspected for the displayed cycle-boundary formulas and Lemma 12.24.2.
The categorical expansions are agent-written, as recorded in the new nodes' `proof_origin`.
LeanSearch was queried for both new statements and returned Internal Server Error; the searches
are recorded as unavailable. LeanFinder and source grep found general homology/subobject tools but
no matching filtered-complex statement. The existing source-library subobject tools were read and
used, and the blueprint searches found no duplicate representative or kernel node.

Edge cases checked: zero complexes and zero filtration steps give zero maps and zero kernels;
r=1 recovers the graded-piece cycle/boundary situation; constant filtrations give zero quotients.
The representative epimorphism statement also works for r=0, since only the quotient index
inequality is used. For general abelian categories, the kernel proof must use epimorphic
refinements rather than assuming quotient morphisms are surjective on arbitrary generalized
elements. Its docstring explicitly records this distinction.

## New nodes

`lem-sp-filtered-complex-representative-epis` is realized by
`Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis` and is fully proved. It gives only the
canonical epimorphic representative maps and their equations. It is strictly part of the original
argument and has no image comparison conclusion.

`lem-sp-filtered-complex-representative-kernels` is realized by
`Sheaf.Algebra.Homology.FilteredComplexRepresentativeKernels` and is the sole new deferred theorem.
It gives only equality of two kernel subobjects. Combined with the independently proved
representative epimorphisms and quotient-map construction, the main module proves the desired
isomorphism and its representative compatibility.

No change record is needed: all existing interfaces are identical, and there are no adaptations.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Independently diffed the original comparison module against the
   repository. The entire existing theorem signature is byte-for-byte identical, as are its
   universe and section assumptions, documentation, visibility, and two public imports.
   Changes are the proof, two proved private helpers, and proof-only imports. There are no
   existing definitions changed, forced adaptations, or change records. The two new public
   theorem signatures agree verbatim with their node records.

2. **Proof and axioms: pass as a decomposition.** Independently compiled all three modules
   together through `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` show exactly `propext`, `Classical.choice`, and `Quot.sound` for
   `filteredComplex_representative_epis`; the kernel theorem and comparison additionally use
   `sorryAx`, as expected from the sole explicitly declared kernel hole. Read every proof:
   the quotient map is constructed by cokernel descent, the two representative maps are
   constructed by image and pullback factorizations, and the final isomorphism is induced by
   mutual descents of epimorphisms with equal kernels. No arbitrary witness is chosen from
   an unproved existence statement. Scanned every delivered Lean file: the only `sorry` is
   the named public kernel theorem; there are no definitions, axioms, unsafe declarations,
   opaque declarations, external implementations, or hidden proof holes added.

3. **Split statements: pass.** Read both new theorem statements and the deferred theorem's
   full docstring argument against the definitions of representatives, cycles, and boundaries.
   The kernel statement is strictly one part of the comparison: it assumes the projection
   equations for given maps and only identifies two subobjects of the representative object.
   The original proof independently constructs the quotient map and uses the fully proved
   epimorphisms before assembling the isomorphism and representative equation. Thus this is
   not a renamed restatement. For zero differential, both kernels are the inverse image of
   the zero-boundary graded class, namely the representatives in F^{p+1}; for constant
   filtrations both target maps vanish and their kernels are the whole representative object.
   Zero complexes give zero objects, and at r=1 the comparison is the identity map of the
   graded complex and the usual cycles modulo boundaries calculation. The epimorphism lemma
   also works at r=0: R is all of F^p and the quotient complex is zero. For arbitrary abelian
   categories the deferred proof correctly uses successive epimorphic pullback refinements,
   rather than assuming surjectivity on generalized elements. Verified the displayed formulas
   on https://stacks.math.columbia.edu/tag/012K independently.

   Searched independently with LeanFinder for inverse images of boundaries under a subcomplex
   quotient map, with Loogle for `CategoryTheory.Limits.kernelSubobject, _ = _`, and with `rg`
   for kernel/quotient, pullback/kernel, and representative formulations in Mathlib and both
   project roots. LeanFinder found only concrete-category and group-homology tools. Loogle
   found general kernel calculus, including `Subobject.pullback_kernelSubobject`; that latter
   name is absent from the pinned local Mathlib sources, so it cannot replace the proved
   private helper here. Existing source subobject tools supply general image/sum calculus,
   not the missing filtered-complex kernel calculation. No duplicate split statement or
   quick closure of the remaining kernel theorem was found.

4. **Pruning and route: pass.** All new imports are used. The public homological-complex
   homology import is needed for the cycle and homology declarations in the new signatures;
   it is not publicly supplied by `FilteredComplexSubquotients`. The subobject extension
   import is proof-only. The original redundant proof-only filtration import is removed and
   recorded above. Every original proof dependency remains used through the quotient,
   filtration, and abelian constructions; no old dependency node is silently dropped.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its inherited unit assignment concerns the
   proper/quasi-finite theorem, and its realized arrays are empty. Neither the unit nor any
   realized unit step is changed or bypassed. The comparison retains its original
   cycle-boundary route and imports no downstream spectral-sequence conclusion.

5. **DAG: pass.** Read all three delivered nodes and compared the existing node with the
   repository: only `proof`, `proof_deps`, and `proof_origin` differ. Their steps describe
   the actual cokernel construction, representative maps, kernel equality, and descent
   assembly. In every node `proof_deps` is exactly the union of the steps' `uses` fields.
   Both new nodes carry source, complete argument, search records, creation metadata,
   blueprint provenance, chapter/unit, and the correct Lean module/declaration/signature.
   The proved and deferred nodes are distinguished accurately in this report.

Second reading changed only this report, adding the independent checks and search findings.
No mathematical repair or proof rewrite was necessary. Closed one original hole and added
one strictly smaller hole; this delivery remains a decomposition with net zero holes closed.

## Second reading by B2

1. **Interfaces and accidental changes: pass.** I diffed the delivered comparison module
against the repository. The existing theorem signature and all existing declarations are
unchanged byte for byte; only its proof and proof-only imports changed. The two additional
modules are new declarations, and no definition, target statement, visibility, or instance
was altered.

2. **Proof and axioms: pass as a decomposition.** I compiled all three modules with
`lcompile.py --all`; they compile without errors or warnings. The only `sorry` is the named
public `filteredComplex_representative_kernels` theorem. No definition contains `sorry`, and
there are no axioms, unsafe, opaque, extern, implemented_by, or hidden proof holes. The
comparison proof constructs the quotient map and the isomorphism by epi descents; it does not
choose data from an arbitrary existence witness. The deferred kernel theorem is the sole source
of `sorryAx` in the comparison's dependency closure.

3. **Split statements: pass.** The representative-epis theorem supplies only the two
epimorphic representative maps and their equations. The representative-kernels theorem assumes
the projection equations and identifies only the two kernel subobjects. Neither restates the
comparison target or asserts its image isomorphism. Their docstrings give complete categorical
arguments and cover zero complexes, constant filtrations, and the r=1 edge case; the epis
statement also permits r=0 as its hypotheses require only the index inequality.

4. **Pruning and route: pass.** The proof uses the existing quotient, filtration, abelian,
and subquotient route, plus exactly the two new intermediate results. The redundant proof-only
filtration import was removed, while all imports used by public signatures remain. No unit step
is bypassed and no old proof dependency is silently dropped.

5. **DAG agreement: pass.** The changed original node records the actual four proof steps and
its two new dependencies. Both new nodes contain matching statements, declarations, sources,
proof origins, search records, creation metadata, chapter/unit, and `lean` records. The proof
dependency lists equal the union of the step uses.

I changed only this report by adding this second-reading section; no Lean proof or node repair
was needed.
