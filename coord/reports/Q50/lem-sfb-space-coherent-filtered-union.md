# Q50: lem-sfb-space-coherent-filtered-union

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-filtered-union.json: statement item, split in five steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-affine-atlas-relation.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-groupoid-equivalence.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-noetherian-groupoid-coherent-approximation.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-kernels-colimits.json: statement-only, unsplit; no Mathlib match.
- citations.json: one literal statement quotation for every step/node pair.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and coherent-colimit/union terminology. FiniteTypeDirected and the module-colimit files concern schemes, not algebraic spaces or equivariant modules, so they do not attach this item. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Problems in the inherited material and changes

The item had no proof. Its assertion agrees with Stacks Tag 07UV, including the important quasi-separatedness in the definition of a Noetherian algebraic space. I have not changed its mathematical statement. I added an explicit reference to def-weil-pbc-category-colimit for its existing colimit notation and added that statement dependency.

The imported ancestry runs through the alteration prerequisite of det-thm-sf-ctf-stability-direct-images proof (3). tools/blueprint_refs.py ancestor returns None for this item, matching its inherited blueprint.from.node = null. I preserve this metadata and give exact supporting places in the new nodes rather than inventing a different ancestor. I read the current literature/blueprint/latest/ unit and direct-images proof (3), as well as the DAG unit/chapter; this is a generic algebraic-space input below the recorded route, not a replacement for the unit route. The new nodes inherit the item's chapter and unit.

## Searches and duplicate audit

Before creating the nodes I searched the whole DAG for 07TU, 07UC, 07UD, 03M3, 03M1, coherent submodules, groupoid modules, Noetherian relations and the proposed ids. I ran blueprint_refs searches for coherent submodules, quasi-coherent, groupoid, 07TU, 03M3, 03M1, Noetherian affine etale presentation and coherent kernels. The blueprint has no matching algebraic-space coherent approximation or flat-groupoid approximation statement. Existing relevant atlas, scheme coherence, coherent subquotient and ringed-site colimit/sheafification statements are reused.

For the item and all four new nodes I ran msearch leanfinder with two different phrasings, loogle, grep, and leansearch; exact queries and returned results are in their mathlib_searches and in search-results.jsonl/searches.jsonl. I read the hits: IsLocallyNoetherian and LocallyOfFiniteType.isLocallyNoetherian are scheme facts; Scheme.Modules.instHasColimits concerns all scheme modules; SheafOfModules presentation and finite-presentation declarations do not give geometric quasi-coherent closure or equivariant approximation. Groupoid search also returns condensed-module AB5 and ordinary ModuleCat filtered colimits; these neither supply equivariant coherent objects nor descent. I inspected Mathlib's Sheaf/Quasicoherent source to distinguish its presentation infrastructure from these geometric assertions. None is an exact statement or one-line specialization.

## Not duplicates

lem-sfb-noetherian-affine-atlas-relation vs lem-sfb-qc-space-affine-etale-atlas: the existing 03H6 node gives an affine surjective etale atlas with no quasi-separatedness hypothesis; the new statement is about the Noetherian relation scheme and the flat qcqs projections of a prescribed atlas. It does not repeat existence of that atlas.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-qcoh-presentation-tensor-equivalence: the existing stack statement starts with cartesian assignments on all scheme charts and concludes descent and tensor compatibility. The new statement starts with module sheaves on the small etale ringed site, gives the small-site/ordinary-scheme-module equivalence and detects coherence on one atlas. The change of module category and coherence criterion are substantive comparisons absent from the existing statement; it cannot be cited for those clauses without a bridge. The new statement is the exact algebraic-space interface of 03M3 and 07UB used here.

lem-sfb-space-qcoh-kernels-colimits vs lem-trf-scheme-etale-quasi-coherent-kernel: both cite 03M1, but the existing statement only proves quasi-coherence of a kernel on the small etale site of a scheme. The new statement allows arbitrary algebraic spaces and gives ambient cokernels and arbitrary small colimits as well. A general ringed-site quasi-coherent kernel theorem would be false, so the geometric hypothesis is essential.

lem-sfb-flat-noetherian-groupoid-coherent-approximation vs lem-sfb-space-coherent-filtered-union: the former is 07TU for arbitrary flat qcqs Noetherian groupoids, not just etale equivalence relations, and only gives a small filtered presentation by coherent objects. The item must construct the atlas, verify the relation hypotheses, identify its module category, prove directedness of actual coherent subsheaves, and prove that their particular canonical union cocone is a colimit. The new node does not state any clause about the poset of subobjects of an algebraic-space sheaf.

lem-sfb-noetherian-affine-atlas-relation vs lem-sfb-space-coherent-filtered-union: the item is 07UV's coherent-submodule union theorem; the new node only checks Noetherianity and flat qcqs properties of a prescribed atlas relation, giving no modules or coherent approximation.

lem-sfb-noetherian-affine-atlas-relation vs lem-sfb-fp-etale-presentation-criterion: the existing node is a finite-presentation criterion over an affine base T with W and R finitely presented over T. A Noetherian space over arbitrary S need not be finitely presented over S; the new node concerns Noetherian scheme atlases and their projections without that relative hypothesis.

lem-sfb-noetherian-affine-atlas-relation vs lem-trf-space-qc-finite-affine-atlas-refinement: the existing node produces an affine atlas by refining a given cover and does not state Noetherianity of its relation or flat qcqs properties of its projections; the new node applies to a prescribed atlas of a Noetherian space.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-proper-space-coherent-derived-image: the existing 0D0R node preserves bounded-below coherent complexes under proper direct image; it does not give descent of small-etale module sheaves to an atlas groupoid or detection of coherence on a single atlas.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-space-coherent-derived-internal-hom: the existing 0D0S node is about bounded-below coherent derived internal Hom, not equivalence of small-etale quasi-coherent modules with groupoid modules or detecting coherence on one atlas.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-space-noetherian-coherent-support: the existing node gives coherent structure modules, coherent subquotients and closed supports; it does not state the presentation-groupoid equivalence or detection of coherence by a single atlas. Its quotient clause is reused in the item's steps 3 and 5.

lem-sfb-space-qcoh-kernels-colimits vs lem-sfb-space-infinitesimal-lift-pseudotorsor: the existing node cites 03M1(6) for one internal Hom in an infinitesimal deformation problem. It does not assert 03M1(1)-(3), the closure of all small-etale quasi-coherent space modules under kernels, cokernels and small colimits.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-space-coherent-kernel-cokernel-extension: this newly synced node gives coherent kernels, cokernels and extensions on a locally Noetherian space, not an equivalence of the small-etale module category with modules on an atlas groupoid or coherence detection on one atlas.

lem-sfb-space-qcoh-groupoid-equivalence vs lem-sfb-space-proper-coherent-higher-images: this newly synced node proves coherence of higher images for a proper map; it does not compare small-etale modules with scheme groupoid modules and cannot supply the descent equivalence used in step 2.

## Review by Q50

I read spaces-cohomology.tex Tag 07UV (lemma-directed-colimit-coherent) in full. Its first paragraph forms sums and images and its second uses 03M3 and 07TU. I also read spaces-properties.tex 03M1 (lemma-properties-quasi-coherent), 03M3 (proposition-quasi-coherent), the Noetherian definition 03EA and the presentation discussion; spaces-cohomology.tex 07UB, 07UC and 07UD; and groupoids.tex 03LI and 07TU including its proof. Thus every new statement has a specific source: relation properties unpack the atlas in 07UV using 03EA/03H6 and etale flatness 0467; the equivalence and coherence test are 03M3/07UB; coherent approximation is exactly 07TU; closure under kernels/cokernels/colimits is 03M1 (1)-(3). The approximation node is left statement-only; its source proof using invariant push-pull intersections is not copied into the item's proof or used as a hidden premise.

Step 1 cites the existing atlas node only for an affine representable surjective etale map, which its statement actually gives, and the new relation node for Noetherian U,R and flat qcqs source/target. Noetherian X supplies quasi-compactness, local Noetherianity, and quasi-separatedness. The latter is necessary for quasi-compact R; I never claim the relation is affine or that the atlas is finite. The groupoid projections are labelled s=pr1 and t=pr0 consistently with 03M3.

Step 2 cites the small-etale/groupoid equivalence, then 07TU's new node after checking both scheme hypotheses and all projection hypotheses in step 1. It uses that equivalence's coherence criterion to descend coherent terms. I spell out why an equivalence carries the universal property of the filtered cocone. The quasi-coherent closure node says that ambient colimits are quasi-coherent, so the colimit is in all module sheaves, not merely in the full quasi-coherent category. The category-colimit definition supplies exactly the universal property invoked. A filtered category here is small and nonempty; there is no colimit over all coherent objects.

Step 3 uses the closure statement for sums and images, the scheme coherent-kernel/cokernel/sum statement for the two-term sum on U, and the descent statement's coherence criterion to return to X. It uses the existing coherent-support statement only for its explicitly stated coherent quotient clause; no support conclusion is needed. The zero object is coherent by its definition. I write the set argument using actual subsets of section sets on a small skeleton; the given universe contains these subobjects. Every two coherent subsheaves are bounded by their coherent sum-image. This proves the directedness clause instead of moving it into a new node.

Step 4 uses the existing general ringed-site colimit statement, whose statement actually gives sheafification of the sectionwise colimit for a variable structure-ring sheaf. The site here admits abelian sheafification. The elementary directed-union calculation gives a presheaf injection into F. The existing exact ringed-site module-sheafification node explicitly preserves kernels, so sheafifying keeps this injection monic. I avoided citing only the definition of sheafification for its exactness and avoided the constant-coefficient local-representatives node, which would not cover O_X-modules.

Step 5 again uses closure for quasi-coherent images and the actual quotient clause of the coherent-support statement. The h_i factor through coherent image subobjects K_i. Compatibility of the maps H_i -> C follows by canceling the monomorphism a from step 4, so the canonical inverse b is constructed by the colimit universal property. Checking ab=1 after all h_i and then canceling a to get ba=1 proves the required isomorphism without assuming that a filtered epimorphic cocone is sectionwise surjective. All cited statements were opened and copied verbatim into citations.json; none is used for a claim only in its proof.

I checked the empty space and F=0 (the indexing poset still contains zero and the atlas can be empty), the identity atlas of an affine Noetherian scheme, non-affine relation schemes, and an infinite-rank quasi-coherent module (no false global finite-generation assertion). The groupoid node permits non-monic transition maps, which the image argument correctly handles. For the new closure node no separation/Noetherian hypothesis was added. For the new relation node local Noetherianity alone is insufficient: quasi-separatedness is explicitly retained. All new statements introduce their objects and define groupoid-module data inline; the cocycle is typed with composition c(a,b)=a after b. No new statement is an elementary sum or a clause of the item. No step exceeds 2000 characters. The off-unit scheme-coherence and ringed-site results are declared as generic tools in split_report.tool_uses; they do not alter the unit's proof route.

## Unfinished work

No stage-1 work on this item remains beyond the required server validation and delivery. The four new statements are intentionally unsplit for later queue work. There are no Mathlib leaves or attachments in this delivery.
