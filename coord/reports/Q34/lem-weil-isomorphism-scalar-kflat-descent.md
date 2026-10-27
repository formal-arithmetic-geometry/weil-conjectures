# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-weil-isomorphism-scalar-kflat-descent.json`: statement item, now split into six steps; no exact Mathlib match for the whole assertion. The statement, statement dependencies and imported provenance are retained unchanged.
- `citations.json`: ten verbatim statement excerpts, one for each step/node citation.
- `report.md`: this direct-delivery review. No new nodes and no new Mathlib leaves.

## Attachments

None. Searching the live `lean/WeilConjectures/` for the exact blueprint tag found no declaration. Concept searches found K-flat and scalar-extension infrastructure, but no declaration proving all clauses for arbitrary compatible ring sheaves and an arbitrary supplied natural comparison. The existing generic Mathlib localization declarations are already represented by `lem-weil-pbc-localization-universal-property`; they do not attach this item.

## Literature wanted

None.

## What was wrong and what changed

The item was an unsplit extraction from Q36's returned tensor-model proof, not a released repair and not an already-reviewed split. Its source correctly identifies the resolving argument but by itself does not state preservation: that is Stacks 0G7E, `sites-cohomology-lemma-pullback-K-flat`. The six steps now cite the existing general preservation theorem, exact-functor localization, ordinary change of rings and resolving-subcategory localization, rather than making new versions of these facts. There is no statement dispute or change of route. The unit is not this node's statement, so no `realized` fields are changed.

The predecessor and blueprint ancestor were read: the parent asks for preservation, a chain comparison and quotient squares, and this child only descends the supplied comparison. The ancestor's first cohomology transport arrow is the intended use of this generic ordinary-derived tool. The current unit text concerns finite-coefficient upper shriek; this item's inherited unit assignment is retained, with the coefficient-independent homological facts declared as generic `split_report.tool_uses` rather than silently replacing the unit route.

## Unfinished work

None at this split level. Existing dependency nodes remain the project's existing obligations. No Lean was written, and no compiler, Lake or build tool was run.

## Search results and reuse

The original item's five Mathlib search records are retained. This worker ran two semantic phrasings, Loogle, grep and LeanSearch through the required `msearch.py`; all succeeded, and their exact queries and returned names are recorded from `searches.jsonl`. The semantic hits concern exact induced derived functors or degree-zero derived functors; none states flat-term K-flat sheaf preservation and normalized descent of this supplied scalar comparison. The Loogle hit `CategoryTheory.Localization.liftNatIso` is the generic tool already represented by the existing localization node. I read `Mathlib/CategoryTheory/Localization/Predicate.lean` lines 278–360 and `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean` lines 29–78. The latter needs an exact functor and therefore does not itself prove the scalar-extension assertion for a nonflat coefficient map.

DAG searches covered K-flat transport, scalar extension, ringed-topos pullback, resolving localization, monoidal equivalence and natural transformation localization, and Stacks tag 0G7D. Whole-blueprint searches were `K-flat`, `isomorphism scalar` and `resolving`; `ancestor` gave `def-weil-global-geometric-frobenius`, which is retained with its original via chain. No blueprint node states this supplied-comparison assertion in another form, so `same_as` is empty.

## Not duplicates

No new nodes. In particular I reused `lem-weil-pbc-ringed-topos-kflat-pullback` instead of a new preservation node, `lem-weil-pbc-site-derived-tensor-descent` instead of a new resolving-localization node, and the Mathlib leaf `lem-weil-pbc-localization-universal-property` instead of a new descent lemma. The ordinary-module node `lem-pc-kflat-extension-of-scalars` was inspected and rejected as a citation for module SHEAVES; the general ringed-topos node has the right objects.

## Review by Q34

I read the item and all eleven of its statement dependencies, the chapter and unit records, the parent tensor-model statement, and the blueprint ancestor. I compared the relevant source text in `sites-cohomology.tex`: Tag 06YS (`lemma-K-flat-resolution`), Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), the construction before Tag 06YU (`definition-derived-tor`), Tag 0G7D (`lemma-factor-through-K-flat`, including its flat-term clause), and Tag 0G7E (`lemma-pullback-K-flat`). I also read `derived.tex` Tag 015F (`lemma-right-derived-exact-functor`) and the localization-subcategory proof, and `categories.tex` Tag 04VG (`lemma-properties-left-localization`). The natural transformation and uniqueness portion is supported by the existing localization node and the Mathlib declarations read above, rather than incorrectly attributed to a sentence of Stacks. No SGA route is used.

For step 1 I opened `lem-weil-pbc-ringed-topos-kflat-pullback`. Its statement is for small ringed topoi, arbitrary ring-sheaf maps, and K-flat complexes WITH flat terms, and concludes both properties after pullback. Here the module-universe small skeleton supplies its size assumption. The first application uses the given ring isomorphism c_R, with the explicit balanced tensor/action-transport identification; the next applications use the identity topos with j_Y and j_X. The third input is good by the first application. Thus neither the result nor its application assumes the coefficient maps are flat.

For step 2 I read `lem-weil-pbc-exact-functor-derived-factorization`, whose statement explicitly preserves all quasi-isomorphisms and gives natural termwise representatives, and clause (1) of `lem-pur-derived-change-of-rings`, which preserves quasi-isomorphisms BETWEEN K-flat complexes. Exactness of G_R,G_S is part of the item, while step 1 supplies K-flat endpoints for applying scalar extension. This does not confuse exact inverse image with a potentially nonexact coefficient change. Homotopy descent is the explicit degreewise equation f-f'=dh+hd after applying the additive termwise functors. It needs no unmentioned homological theorem.

For step 3 I opened `lem-weil-pbc-site-derived-tensor-descent`. I take its actual first assertion, W_R^{-1}P_R equivalent to D(R), not a claim hidden in its proof and not just its two-variable natural-transformation clause. This gives the one-variable localization required here. The full universal-property statement of `lem-weil-pbc-localization-universal-property` then supplies precomposition fully faithfulness. Composition with the stated equivalence is a direct equivalence-of-functor-categories argument. The size hypothesis is unchanged from the item.

For step 4 I checked clause (2) of `lem-pur-derived-change-of-rings`, including the canonical model maps, and the exact-functor node's natural factorization isomorphism. They give a_P and d_P on the good homotopy category; the hypotheses for computing C_X are precisely the goodness of G_RP established earlier. I explicitly form d_P^{-1}[b_P]a_P, so the normalization is the supplied b and its own naturality, with no assumption about a canonical chain comparison or quotient maps.

For step 5 the localization node states existence AND uniqueness of a lifted transformation and that identities and composition are respected. Descending the inverse supplies invertibility; it is not inferred merely from objectwise existence on unrelated resolutions. Step 3 supplies its localization hypothesis.

For step 6 the same exact-functor node makes G_Rs a quasi-isomorphism, a clause the item expressly requires. Clause (2) of ordinary change of rings gives the canonical resolution model maps. I wrote the maps for a general resolution s as a_s=a_P A([s])^{-1} and d_s=d_P B([s])^{-1}; naturality proves the desired equation, not an unspecified claim of transport. The two-resolution square follows by substitution and the third-resolution identity by cancellation. All non-elementary input in this step is in those two cited statements.

I checked B through E of `coord/delivery-errors.md` against these files. There are no statement-only new nodes to accidentally fill with proofs, no new definition, no unchecked duplicate, and no invented search. Every cited node's actual statement was opened, with verbatim portions in citations.json; dependency closures do not reach this item. The proof carries the normalization and independence argument instead of moving the item to a new lemma. Each step is below 2000 characters. The needed sources are present and tags were checked in `literature/stacks-project/tags/tags`.

For small cases, when g and both coefficient maps are identities the construction gives localization of the supplied b, so a nonidentity natural b is not inadvertently forced to be canonical. A zero complex and the empty scheme give the unique zero-object comparisons. With the nonflat map Z to Z/2 on a point, flat-term K-flat resolutions still compute derived extension, while tensor of an arbitrary acyclic complex is never assumed exact. Arbitrarily unbounded good complexes are covered because 0G7E and the resolving theorem have no bounds; no truncation or convergence argument is introduced. Ring isomorphisms c_R,c_S may be nontrivial automorphisms; the action-transport identification uses those actual maps. I corrected no mathematical statement, but replaced prospective specialized preservation/descent lemmas by the existing more general nodes and made the canonical resolution equations explicit.
