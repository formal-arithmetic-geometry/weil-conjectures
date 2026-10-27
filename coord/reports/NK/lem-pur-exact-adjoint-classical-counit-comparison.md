# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-exact-adjoint-classical-counit-comparison.json: item, statement preserved, six proof steps, status split.
- dag/nodes/sec-smooth-purity/lem-pur-tstructure-lower-bound-hom-test.json: statement, Mathlib leaf CategoryTheory.Triangulated.TStructure.isGE_iff_orthogonal, Mathlib/CategoryTheory/Triangulated/TStructure/TruncLTGE.lean:617.
- citations.json: verbatim statement quotations for every citation in the item's steps.

## Attachments

None for the item. Searches of lean/WeilConjectures for its exact blueprint tag, counit comparison and t-exact right-adjoint terminology found no declaration stating the whole item. CategoryTheory.Triangulated.TStructure.isGE_rightAdjoint_obj in WeilConjectures/CategoryTheory/Triangulated/TStructure/Adjunction.lean:39 proves an additive bounded-amplitude variant of the lower-bound clause only. It neither states the entire item nor gives the new leaf's general orthogonality equivalence. It is not an attachment. Its source was read; this delivery's singleton-Hom argument avoids assuming F.Additive.

## WANTED

None. The blueprint source, Stacks categories.tex, BBD and the Mathlib source used here are available locally.

## Audit of the imported item

No statement correction and no route change. The imported source place points to the first localization triangle of sk-prop-a1. That paragraph supplies the geometric context, not a proof of this abstract categorical calculation. Accordingly proof_origin.by remains agent. I read the unit and chapter records, the current main-20261015 sk-prop-a1 proof, the ancestor's current proof, and the parent lem-pur-closed-finite-adjoint-counit-transport. This item is the categorical tool used by that parent's second and third steps. Its first clause is proved by orthogonality; its comparison equation is proved from the actual specified unit and counits. No SGA source is used.

The lower-bound claim needs no triangulatedness or additivity assumption on F: an adjunction identifies Hom(A,GN) with a singleton, hence Hom(A,GN) contains only its zero morphism. Trying to prove the assertion by preservation of zero under a transpose would impose an unnecessary assumption. Nor is a right adjoint to P needed anywhere. No boundedness assumption on U_X is used: U_XS_XN is isomorphic to N by the given unit. The stated lower-bound preservation for S_T is retained although this calculation does not need its full strength.

## Search record

All new searches were made with the prescribed msearch.py command, and searches.jsonl contains their actual results. No search result was fabricated or inferred from a failed service. The item was searched by upper/lower-bound adjunction language and by a second counit/inverse-unit phrasing, plus Loogle and grep. Generic adjunction/triangulatedness results and inv_map_unit do not state the entire item. For the new leaf, semantic searches found the t-structure and zero-morphism APIs; the exact Loogle query found isGE_iff_orthogonal. The prescribed grep found its declaration at line 617; I read lines 606-624. Set n₀=a-1 and n₁=a, with (a-1)+1=a: this is exactly the node, with no boundedness or nondegeneracy hypothesis. The leaf's records use the searches for its own statement, not the earlier searches of the whole item.

Before creating the leaf I searched the whole DAG for orthogonality, lower bounds, truncation triangles, right-adjoint/t-exact terminology, isGE_iff_orthogonal, right orthogonal and the title. I searched the whole blueprint using blueprint_refs.py search for orthogonal, t-structure, orthogonality criterion, right adjoint, counit comparison and lower bound, and obtained the nearest ancestor using blueprint_refs.py ancestor. No blueprint node states the new equivalence. I also read the existing one-way derived orthogonality node and the t-structure extension-closure node. Searching Lean for isGE_iff_orthogonal found applications of the Mathlib lemma, not a project declaration stating its full equivalence.

## Not duplicates

lem-pur-tstructure-lower-bound-hom-test vs lem-pc-derived-tstructure-orthogonality: the existing node states only that maps from an upper-bounded object to a strictly higher lower-bounded object vanish; the new leaf supplies the converse implication detecting the lower bound from all such vanishings, for arbitrary t-structures.
lem-pur-tstructure-lower-bound-hom-test vs lem-sbc-tstructure-extension-closure: the latter states zero-object membership and closure under distinguished extensions, not the orthogonality characterization.
lem-pur-tstructure-lower-bound-hom-test vs def-weil-t-structure: the definition states the t-structure axioms and truncation data, not the converse orthogonality theorem.
lem-pur-tstructure-lower-bound-hom-test vs lem-per-qbar-middle-tstructure: that node gives a particular perverse t-structure and its orthogonality characterization on constructible Qbar_l objects; this leaf applies to arbitrary t-structures, including ordinary unbounded derived categories, with no geometric hypotheses.

## Review by NK

I checked the actual source statements and the cited node statements with the files open. BBD, Faisceaux pervers, 1.3.4 on printed p. 30 explicitly identifies the lower half of a t-structure as the right orthogonal of the previous upper half. The preceding 1.3.2(i) is the standard derived t-structure. I extracted PDF pages 30-34 and read the relevant paragraphs, rather than trusting the older node's source pointer. The new leaf is exactly this characterization translated from 0,1 to a-1,a; the Mathlib source at TruncLTGE.lean:617-622 verifies it for arbitrary t-structures. The statement introduces T,t,a,M and quantifies over all test objects and all maps, cites its t-structure definition, contains no proof sketch, and has no proof dependencies. It is strictly smaller than the item: it mentions no adjunction or comparison functors.

For Step 1 I read lem-pc-derived-tstructure-orthogonality, whose statement says every map A to B is zero for n<m. Here its objects are FA and N, and n=a-1<m=a, exactly its hypotheses. The new leaf is then applied to GN and JN in the standard t-structure, not to any geometric or perverse category. The adjunctions are hypotheses of the item, and Stacks Tag 0037 (categories.tex, definition-adjoint and the following formulas) says they give natural Hom bijections. A singleton Hom set remains a singleton under a bijection; since the target category has zero morphisms, its sole morphism is zero. This elementary observation is what completes the argument without assuming additive adjunction data.

For Step 2 I read def-sbc-standard-tstructure-derived-category: its classes are strictly full and described by vanishing cohomology. It therefore says exactly what is used to put U_XS_XN in the same lower-bound class as N. Both D_N and E_N are bounded below before lambda is ever evaluated at them. Images and composites of isomorphisms have explicit inverses (apply the functor to the inverse and reverse the composite), so no extra existence lemma is hidden in beta or alpha.

Step 3 is the stated triangle identity followed by composition with S_X(r_N); the domains are S_XN and S_XU_XS_XN, and its result is e at K_N=S_XN. Stacks Tag 0037's explicit transpose formulas explain these identities; the triangle identity itself is expressly supplied in the item's hypotheses. Step 4 uses counit naturality at r_N and det-sp-unique-right-adjoint. I read that node's full statement: it supplies the equation epsilon^J_N composed with F(gamma_N) equals epsilon^G_N and the naturality of gamma, with no additional full-faithfulness hypothesis. The composite F(gamma_N) F(G(r_N)) is F(beta_N), with the correct source E_N and target D_N. Step 5 is the given lambda's naturality at beta_N followed by its inverse components; its output P(alpha_N) has source PS_ZE_N and target PS_ZD_N, exactly the domains needed for the final equation. Step 6 spells out inverse-unit naturality and beta naturality, and explains the restrictions that make the composites natural. These last steps use only hypotheses, category identities, functoriality and the cited normalization; they do not hide another theorem.

I tested the new leaf for the zero object, the zero category, arbitrary positive and negative a, and the standard t-structure on vector-space complexes: an object with nonzero cohomology below a fails the test, while degree a is allowed. No boundedness or nondegeneracy assumption is needed; the Mathlib proof uses truncation rather than cohomological conservativity. For the item I checked the identity-adjunction case (all comparisons reduce to the given lambda transport), N=0, and arbitrary nonadditive comparison functors S_T and P. Only preservation of identities, composition and inverses is needed of those functors. I verified every displayed composite's source and target, especially the direction of lambda inverse and r_N. The statement was not weakened. No step exceeds 2000 characters. The new node has complete provenance, source and honest searches; all quotes in citations.json are copied verbatim. I corrected the drafting script's quoting error before any node was written; no mathematical correction was required.

## Unfinished work

None for the one-level split. The new node is already a Mathlib leaf. Only stage 1 was performed; no Lean file was written and no compiler, Lake or build tool was run.
