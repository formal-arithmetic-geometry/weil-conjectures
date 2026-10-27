## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/def-sfb-pinned-split-root-realization.json — definition; split into existing statement dependencies, with the component notions explained explicitly; no whole-item Mathlib match.
- citations.json — the empty list, because this definition has no proof steps.
- report.md — this report and direct-delivery review.

## New nodes

None. There are zero new nodes and zero Mathlib leaves. A definition has no existence proof to split: its work is identifying its constituent notions (stages/1-dag.md §3(2)). I did not turn the definition's clauses into new lemma nodes. Auxiliary search probes for component definitions were abandoned in favour of the existing DAG and explicit elementary formulas; their unmodified search logs are retained under search-probes/, and no node is delivered for them.

## Attachments

None. Searching lean/WeilConjectures/ for the blueprint tag, pinned/PinnedSplit, RootDatum/rootDatum and reductive found no project declaration of the item. The hits for “pinned” concern unrelated normalizations; the reductive hits concern characteristic-zero Lie algebras, not group schemes over rings. In particular there is no project declaration proving all the item's clauses without sorry to attach.

## WANTED

WANTED: Brian Conrad, Reductive Group Schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Definitions 1.3.3, 3.1.1, 5.1.1, 6.1.1 and isomorphism terminology p.187, for def-sfb-pinned-split-root-realization. The PDF is not listed locally; these places were read online. No local literature file or repository file was written. This is Conrad's exposition, not an SGA source.

## What changed and what was wrong

The original was already correctly a definition with no existence assertion. It was unsplit and several descriptions were implicit. I preserved its mathematical conditions and expanded the formulas: closed subgroup, geometric fibre, monomial character/cocharacter, based-datum isomorphism, tangent module, weight submodule and pinning-compatible isomorphism. The lattice variance is now explicit: if u:M→M' carries the based data forward, the map on tori is D_A(u^{-1}), so the pullback on characters is u^{-1}.

I replaced lem-sfb-reductive-borel-pair-structure by lem-sfb-reductive-rank-one-reflections for the specific rank-one SL2 construction of the geometric coroot. The former states the resulting root datum but not that construction; the latter states v_alpha and alpha^vee(t)=v_alpha(diag(t,t^{-1})) and its uniqueness. Added existing closed-immersion, dual-number, tensor-product and direct-sum definition nodes. No field-only definition was applied over an arbitrary ring. In particular def-sc-group-scheme and def-sc-scheme-tangent-space were read but not used to supply an arbitrary-base notion they do not state.

This is an explicit clarification, not a change of the scope or a weakening of the definition. No existence, canonical classification, Borel construction, or preservation under nonflat base change has been inserted: those remain in the separate existing theorem nodes. Nothing remains unfinished for this stage-1 definition; a local copy of Conrad remains wanted.

## Searches and blueprint

The item's inherited searches and results were retained. New searches are recorded verbatim from searches.jsonl, including both natural-language phrasings. LeanFinder and LeanSearch give RootDatum, RootPairing.Base, RootPairing.IsReduced and unrelated polynomial/Clifford facts. Loogle gives RootDatum. Reading Mathlib/LinearAlgebra/RootSystem/Defs.lean:82–109, Base.lean:70–78 and Hom.lean:261–263 confirms these concern abstract root pairings and their equivalences, not reductive group schemes and their tangent pinnings. Base also has coroot-base fields, so identifying the entire composite with it is not a one-line specialization. The valid AlgebraicGeometry grep has no pinned/reductive match; the targeted root-system grep locates the relevant component definitions. CategoryTheory.GrpObj (Monoidal/Grp.lean:43) supplies the group-object component only. No whole-item leaf is claimed.

One Loogle query used the unqualified name GrpObj and returned an unknown-identifier diagnostic; it is recorded as unavailable, not an absence result. One redundant grep used the invalid Mathlib/AlgebraicGeometry subdirectory (the wrapper already adds Mathlib); its zero hits are expressly discarded as evidence. The successful AlgebraicGeometry search and targeted whole-Mathlib search replace it. No query was invented.

Whole-DAG searches used the key phrases finite reduced, based root datum, pinned split realization, coroot and the Conrad URL/definition numbers. blueprint_refs.py searches for pinned, root datum, root and group scheme found no equivalent blueprint item. The latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md were read. The definition supports the existing reduction branch through reductive-etale-integral-models; no chapter or unit route was replaced. The ancestor command returns None for this created node, so the inherited null from.node and full via chain are retained, with its precise place and same_as=[] and split_report.blueprint filled. The remote review_split check passed this provenance.

## Not duplicates

No new nodes are proposed. Existing pinned-split-root-classification and pinned-split-root-base-change are theorems using this definition, not its replacements. integral-split-root-datum is an integral-model structure theorem, not arbitrary-ring pinned data. ring-diagonalizable-group is reused. The field-only group-scheme and tangent definitions cannot replace the ring formulas. No unrelated root-system theorem is restated as a node.

## Review by Q116

I read Conrad Definition 1.3.3 on printed p.27, Definition 3.1.1 on p.81, Definition 5.1.1 and Example 5.1.2 on p.136, and Definition 6.1.1, Remark 6.1.2 and the isomorphism terminology on pp.186–187 online. For general group and closed-subgroup terminology I read Stacks groupoids.tex, labels definition-group-scheme (022S) and definition-closed-subgroup-scheme (047D). There is no new-node source to review. I compared every clause to its source; the arbitrary nonzero ring, possibly disconnected base, constant lattice labels, globally free root lines and specified simple generators all remain required. Spec A is nonempty because A is nonzero. Finite presentation is the existing node's locally-finitely-presented plus quasi-compact/quasi-separated convention; affineness is retained. No Noetherian assumption is used.

There are no numbered proof steps: proof=[], proof_deps=[], proof_origin=null and citations.json=[] are intentional for this definition. I read the full statements of all its dependencies. def-pc-scheme and affine-spectrum give schemes and Spec; fibre-product gives the products and fibres; affine-morphism, locally-finite-presentation, smooth-morphisms and connected-scheme supply precisely their indicated structural predicates. ring-diagonalizable-group gives A[M], e_m and the Hopf operations, including D_A on lattice maps. closed-immersion supplies the meaning of the torus inclusion. dual-numbers permits an arbitrary commutative ring. module-tensor-product and direct-sum-modules give the constructions appearing in the coaction and decomposition. rank-one-reflections gives exactly the coroot formula and uniqueness over each algebraically closed geometric field in every characteristic, with G reductive and T maximal as required here. The replaced Borel-pair citation did not give that formula. No proof text of a cited node is being used in lieu of its statement.

The tangent formula is directly checked in coordinates: multiplying c(b)+epsilon d(b) and c(b')+epsilon d(b') gives c(bb')+epsilon(c(b)d(b')+c(b')d(b)), so precisely the displayed derivation identity makes it an algebra map. The pointwise module operations preserve that identity, including over nonreduced rings. Weights are defined by the full coaction, avoiding the loss of character information after differentiation in characteristic p. The displayed direct sum and freeness are conditions imposed on the realization, not a covert assertion that arbitrary reductive groups have free root spaces. The definition neither selects data by a sorry existence theorem nor asserts a canonical choice of generators.

For edge cases I tested M=0, Phi=Delta=empty, and the trivial group, and M=Z^r with G=T=D_A(M) and empty roots: the pinning condition is vacuous and the direct sum reduces to Lie(T). I tested SL2 in characteristic two: its root character is still the nonzero lattice element 2 although its differential is zero, so the coaction formulation is necessary. I checked the disconnected-base example PGL2×Gm on one component and GL2 on another with the identified torus: the coroots differ, and the constant-coroot requirement correctly excludes a single common realization, as in Conrad Example 5.1.2. The fixed lattice map also disallows component-dependent automorphisms. The dual-number formulas do not require reducedness or Noetherianity of A. Roots need not span M_Q, so central tori are retained.

Against delivery-errors B–E: every object is bound, all extra terminology is defined inline or supplied by a dependency read above, TeX has single mathematical escapes, and no tag substitutes for a definition. C1/C4 were checked by reading those statements, with the one precise coroot citation corrected. There is no relabelled theorem split, circular existence argument, long hidden proof step, or off-unit proof tool. Sources and inherited fields were preserved; no SGA source, Lean writing, compiler or Lake invocation was used. The remote review_split check passed before delivery; the full delivery dry run follows.
