# Stage-1 delivery: lem-sfb-quotient-map-cartesian-action-groupoid

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-quotient-map-cartesian-action-groupoid.json: statement, split; no Mathlib match. Statement retained; added the existing algebraic-space fibre-product theorem to statement dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-stackification-two-fibre-products.json: statement, unsplit; no Mathlib match. The general compatibility of stackification with 2-fibre products (04Y2); no proof or proof dependencies.
- citations.json: verbatim statement excerpts for every proof-step citation.

## Attachments

None. Searches by the exact item tag and by quotient/cartesian/action-groupoid and stackification concepts in lean/WeilConjectures found no declaration stating this item or the new lemma. Ordinary scheme pullbacks and unrelated conormal quotient comparisons do not state them. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are present locally.

## Source error

The item's statement is correct and unchanged. Stacks spaces-groupoids.tex, Tag 04Y4, has notation slips in its proof: it sometimes writes the discrete fibred groupoid of U rather than U', calls the arrow r' a point of R rather than R', and says that its objects correspond to points of R'' rather than U''. The displayed triple has two independent coordinates u and r', subject to f_0(u)=t'(r'), so its parameter space is A=U''. R''=B instead parametrizes arrows. For example, for a homomorphism of one-object groupoids G to H, A=H while B=G times H; nontrivial G distinguishes the two. The split uses the correctly typed coordinates throughout. These are proof notation corrections, not a change to the source theorem, the item or its hypotheses.

The existing blueprint ancestor chain ends in null, as tools/blueprint_refs.py ancestor reports. I retained that maintainer-owned value and the inherited creation route; the split report records the current latest direct-image proof paragraph (3). The chapter and unit records were read and unchanged. This lemma is a supporting groupoid calculation for the existing alteration/moduli route, not the unit's key statement.

## Searches and reuse

The item's existing five Mathlib searches were read with their results. They concern base-change stability of morphism properties, ordinary categorical and scheme pullbacks, product groupoids, and contain no quotient-stack comparison. They are retained as historical records rather than attributed to this session.

For the new node I ran the required msearch.py command twice with distinct semantic phrasings using LeanFinder, once with LeanSearch, once with Loogle, and once for a whole-Mathlib grep. All ran successfully. Both semantic phrasings returned predicates and descent functors for existing stacks. I read Mathlib/CategoryTheory/Sites/Descent/IsStack.lean: IsStack and isStackFor encode effectiveness of descent, not construction of associated stacks or preservation of 2-products. The LeanSearch candidate sheafifyCompIso was read in CategoryTheory/Sites/CompatibleSheafification.lean: it compares ordinary sheafification with postcomposition by a limit/colimit-preserving functor; this is not groupoid stackification. Loogle returned no matches; the grep stackif|stackify|associatedStack returned none. Exact tools, queries and results are recorded in the new node and searches.jsonl.

Before creating the new node I searched the whole DAG for 04Y2, 04Y1, stackification-fibre-product, stackification and fibre-product language; no node states this general result. Blueprint searches for stackification, stackify, stackification fibre, quotient groupoid, and 2-fibre product found no counterpart. The broader fibre product search returned ordinary scheme and cohomological base-change nodes, which do not state it. The latest blueprint was also searched. Existing lem-sfb-quotient-stack-invariant-base-change has a discrete invariant algebraic-space base, and cannot be used for base change over a quotient groupoid. Existing local-description and equivalence nodes supply different stackification tools; they do not assert 04Y2. Existing lem-trf-space-fibre-products-etale-covers is reused for algebraic-space closure rather than duplicated.

## Not duplicates

There is no existing node whose source cites 04Y2 or 04Y1. The new general stackification node does not restate the action-groupoid item: it has no algebraic spaces, no morphism of internal groupoids, and no formulas for A, B or their operations. Those coordinates and formulas are proved in the item's steps. Conversely the general stackification assertion is not a two-line consequence of the definitions; 04Y1 proves it by a separate local full-faithfulness and local-essential-surjectivity argument.

## Review by Q106

I read Stacks spaces-groupoids.tex at 04Y4, including the construction immediately before the lemma and every paragraph of its proof. For the new node I read stacks.tex at 04Y2 and the full proof of its general-category antecedent 04Y1. The latter first constructs the projection-compatible comparison and then proves it fully faithful and locally essentially surjective; the new node states that comparison, without copying its proof into a statement. I also read 02ZP and 0436 for the existing stackification local-description theorem, and spaces.tex 02X2 for the existing algebraic-space fibre-product theorem. No SGA source is used.

Step 1 uses the actual statement of lem-trf-space-fibre-products-etale-covers: its first sentence asserts that the sheaf fibre product of arbitrary algebraic spaces over S is an algebraic space. It applies twice, with common target U', and needs no etaleness, quasi-compactness or finiteness. I do not use the later etale-family clause. The statement of def-sfb-stable-pointed-moduli-groupoids explicitly defines the fibrewise 2-product and its morphism compatibility, so it really provides K and not merely the notion of a moduli stack. This cross-unit space theorem is declared as a generic tool in split_report.tool_uses.

Step 2 uses that same explicitly stated 2-product definition. Since U' is discrete, the first arrow must be an identity, forcing equal u' coordinates. The compatibility equation is exactly f_1(r) composed with r'_2 equals r'_1. This verifies both directions of the arrow bijection, including which primed arrow is retained. The object inverse is explicitly (u,r') mapped to (s'(r'),u,r'); no representability or quotient theorem is assumed here.

Step 3 uses the groupoid laws stated in def-a1-groupoid-scheme, with algebraic spaces as the item explicitly prescribes, and the definition of maps of algebraic spaces as natural transformations in def-trf-algebraic-space. I recomputed inverse and composite, including the composability conditions and the f_1 composition identity. They coincide with the ordinary groupoid operations on K; consequently every law follows without adding a separate node for a restatement of the item's operation clause. Restriction is precomposition on all coordinates, so the isomorphism is over the site, not merely a collection of unrelated fibre equivalences. These are elementary substitutions into the supplied definitions.

Step 4 uses the new 04Y2 statement, not an existence theorem for plain category pullbacks. Its hypotheses allow arbitrary fibred groupoids in the fixed larger universe, so P, P', and the discrete U' sheaf meet them on the skeleton of the big fppf site. Algebraic spaces are fppf sheaves by the cited definition: discrete descent therefore glues objects and identities. The new node explicitly permits a stack factor to be its own stackification and asserts compatibility with the projections and raw comparison. The existing local-description theorem explicitly applies to presheaves of groupoids, so its stackifications are precisely [A/B], [U/R] and [U'/R']; no algebraicity of these quotient stacks is inferred or needed. The raw arrow r' supplies the stated 2-isomorphism and fixes its direction. Every cited node was opened and its statement checked, and citations.json copies the relevant text literally.

For B1--B9, the single new node has a self-contained statement, names the site and universe, defines the triples and arrow condition, cites its notion dependencies and source tags with exact labels, has empty proof and proof_deps, and records only searches actually run. It has no claimed Mathlib match or attachment. Its blueprint from/via follows the printed inherited ancestor. For C1--C8, the non-elementary facts used are algebraic-space fibre-product closure and general stackification compatibility, both explicitly cited; no source theorem is invoked merely by its tag. All used-node statement excerpts are in citations.json. Existing definition and local-description nodes are used only for their actual contents; there is no dependency cycle back through the new node. For D1--D5, the raw object/arrow calculations remain in the item, while the new lemma is a genuine general stackification theorem, not an item clause or a renamed whole conclusion. For E1--E7, I checked all domains, target conventions, comparison direction and operations and corrected the source's notation slips as described above. Every step is shorter than 2000 characters.

Small cases checked: U empty makes both sides empty; identity groupoids reduce the result to ordinary object base change along f_0; f the identity gives the usual atlas relation; one-object groupoids G to H give objects H with the left G-action through f and arrows G times H, so nontrivial stabilizers are retained; arbitrary nonflat f_0 changes none of the coordinate arguments. For 04Y2 I checked a discrete sheaf factor (its identity is a stackification), the identity cospan (both sides are a(X)), and empty fibred groupoids; no nonempty-cover or representability hypothesis has been smuggled in.

## Unfinished work

The general 04Y2 node is intentionally statement-only for its own stage-1 item. No part of the present item's proof remains omitted; the required dry run and direct push follow this report.
