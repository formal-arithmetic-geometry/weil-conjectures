# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-ind-presheaf-fibration-accessibility.json`: repaired item statement source, proof, and dependencies.
- `dag/nodes/sec-six-functors/lem-coef-ghn-ind-presheaf-cartesian-realization.json`: repaired GHN relative-cone classification node.
- `dag/nodes/sec-six-functors/lem-coef-ind-right-adjoint-coherent.json`: statement-only coherent right-adjoint Ind node.
- `citations.json`: refreshed verbatim citations for all proof steps.
- `report.md`: this repair report.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, the blueprint tag, and the Ind/presheaf accessibility terminology; no sorry-free project declaration states the item or either new support statement.

## WANTED:

- `WANTED: Gepner–Haugseng–Nikolaus, arXiv:1501.02161v3, Definition 10.4, Proposition 10.5, Corollary 9.17, Lemmas 10.6 and 10.7, for the source theorem; the source is available online but is not archived in literature/.`

## Not duplicates

- `lem-coef-ghn-ind-presheaf-cartesian-realization` vs `lem-coef-ind-presheaf-fibration-accessibility`: the support node gives the relative-cone conditions and Cartesian-fibration classification, while the item constructs the coherent Ind diagram, the presheaf extension and element-slice formula, and proves accessibility.
- `lem-coef-ghn-ind-presheaf-cartesian-realization` vs `lem-coef-presentable-infinity-adjoints`: the support node is the GHN relative-cone classification; the existing node is the general presentable localization theorem used in the item's accessibility step.
- `lem-coef-ind-right-adjoint-coherent` vs `lem-coef-ind-presheaf-fibration-accessibility`: the new node supplies the explicitly defined coherent right-adjoint Ind diagram used to state the item's extension; the item additionally constructs the presheaf extension and accessibility conclusion.

## Source error

`STATEMENT-DISPUTED: the imported item required an uncountable regular cardinal, but GHN Definition 10.4 and Proposition 10.5 allow an arbitrary infinite regular cardinal. The small case $\lambda=\aleph_0$ is allowed by the source. The item is corrected to “an infinite regular cardinal,” and its proof cites the arbitrary-cardinal coherent Ind construction.`

The earlier support statement was also false: it imposed an absolute fiber-limit condition and treated cocartesian edges as equivalences. The repaired node uses GHN's relative limit over the cone point and the pullback square for cocartesian edges. The one-object test $A=*$, $F_0(*)=C$, with a two-point presheaf value at the cone point distinguishes the relative condition from the false absolute one.

## Review by Q23

I read the GHN v3 source at Definition 10.4, Proposition 10.5 (including clauses (i)–(iii)), Corollary 9.17, and Lemmas 10.6 and 10.7, together with the item blueprint ancestor and every cited DAG statement. The source labels in both node records now name Proposition 10.5 and distinguish the relative-limit lemma (10.6) from the locality/accessibility lemma (10.7).

The item statement agrees with Definition 10.4 and Proposition 10.5: $\lambda$ is infinite regular; $H(a)=\operatorname{Ind}_\lambda(F_0(a))$; each reverse transport is the explicitly defined right adjoint; the extension is the limit-preserving extension of $H$; the category-of-elements formula and accessibility conclusion are retained. The support node has the same $A$, $F_0$, cone, and universe hypotheses and now states only the two GHN relative-cone conditions and their Cartesian-fibration classification. The new coherent-Ind node states the right-adjoint construction at the same arbitrary regular cardinal.

Step 1 uses the statements of `lem-coef-ind-kappa-presentability`, `lem-coef-ind-kappa-extension`, `lem-coef-presentable-infinity-adjoints`, and `lem-coef-ind-right-adjoint-coherent`; I checked that they provide compact Ind fibers, the filtered-colimit-preserving extension, the mapping-space right adjoint, and coherent contravariant higher simplices with the required variance. Step 2 uses the free-cocompletion equivalence after opposites, whose restriction equivalence gives the coherent limit-preserving extension and uniqueness. Step 3 uses the representable-slice density statement, which supplies the essentially small category of elements and the colimiting coherent cocone.

Step 4 uses cocartesian straightening and the repaired GHN support statement for the relative-cone classification. I checked that condition (i) is the pullback square through the cone points and condition (ii) is the relative $(K^{\triangleleft\triangleright})^{\mathrm{op}}$ limit. The locality maps form a small set because the cocartesian edges and all $\lambda$-small fiber diagrams are small in the fixed universe. `lem-coef-infinity-presheaf-presentability` gives the ambient presentable presheaf category; `lem-coef-presentable-infinity-adjoints` gives the presentable reflective local subcategory for these tests; and `lem-coef-infinity-reflector-accessibility` gives accessibility of the local subcategory and inclusion-after-reflection. For a filtered diagram of local objects, the local colimit is the reflected ambient colimit, so the inclusion preserves filtered colimits. Pointwise colimits make restriction accessible. Step 5 applies the straightening/unstraightening equivalence in the containing universe and transfers fibers, transports, and accessibility.

For the new support node I checked the relative cone pushout, the pullback cocartesian condition, the relative fiber limit condition, and the Cartesian classification against the cited GHN propositions and lemmas. For the coherent-Ind node I checked the explicit $u^*$ right adjoint, filtered-colimit preservation, contravariant variance, and higher simplices against Definition 10.4. I tested the repaired support condition on $A=*$, a terminal fiber, identity cocartesian edges, an empty fiber diagram, and a coproduct-shaped diagram. Searches of the whole DAG and blueprint found no duplicate statements. Every quote in `citations.json` is a literal substring of its cited statement, and every step use occurs in `proof_deps`.

## What was wrong in the imported split

The support node had incorrectly absorbed the accessibility/locality argument, included a proof sketch in its statement, and wrote the extension as a limit-preserving extension of the ill-typed expression `Ind_lambda ∘ F_0^op`. I removed the accessibility clause and proof sketch from that node, defined the right-adjoint Ind functor explicitly there, added its coherent-Ind dependency, and moved the locality-map argument into item step 4 with the two required accessibility citations. I corrected the source places to include Proposition 10.5 and to distinguish Lemmas 10.6 and 10.7. The report and citations now describe this repaired file set.

## What I could not finish

None at stage 1. No Lean, compiler, Lake, build, live project, or launcher file was touched.

## Earlier second reading (a previous round; superseded)

- Statement: checked GHN Definition 10.4 and Proposition 10.5, including clauses (i)–(iii), and corrected the source labels and regular-cardinal hypothesis.
- Step 1: checked all four Ind and adjunction statements and their hypotheses, including the explicit right-adjoint variance and higher coherences.
- Step 2: checked the free presheaf cocompletion equivalence after taking opposites.
- Step 3: checked the representable-slice density statement and its essential-smallness and colimit claims.
- Step 4: checked the GHN relative-cone classification, the small locality test set, and both accessibility nodes; the locality argument is now in this step rather than in a support-node statement.
- Step 5: checked the straightening/unstraightening equivalence and universe qualification.
- New node `lem-coef-ghn-ind-presheaf-cartesian-realization`: checked its cone pushout, pullback condition, relative limit condition, and classification; removed the former accessibility proof sketch.
- New node `lem-coef-ind-right-adjoint-coherent`: checked its explicit right-adjoint Ind construction and arbitrary-regular-cardinal hypotheses.
- Checked DAG and blueprint searches for duplicates, all citation quotes, and the dependency union.

## Second reading by Q23

- Item statement: checked GHN v3 Definition 10.4 and Proposition 10.5, Corollary 9.17, and the presheaf universal property; the infinite regular cardinal, small fibers with $\lambda$-small colimits, right-adjoint variance, limit extension, element-slice formula, and accessibility agree. The earlier report's references to Proposition 10.5 clauses (i)–(iii) and to Lemma 10.7 as an accessibility lemma were incorrect: Proposition 10.5 is unnumbered internally, Lemma 10.6 is the small-locality lemma, and Lemma 10.7 concerns existence of colimits in a cocartesian total category. The delivered source fields now name only the relevant places.
- Step 1: read all four cited Ind and adjunction statements. The final clause of `lem-coef-ind-kappa-extension` supplies preservation of all small colimits after composing $F_0(f)$ with the target Yoneda embedding; both Ind categories are presentable. Made that composition and the required clause explicit. The uniform coherent-Ind node supplies the right adjoints and all higher simplices, at arbitrary infinite regular cardinal.
- Step 2: read the free-cocompletion restriction equivalence and `lem-coef-cat-infinity-colimits-cartesian-closure`; the latter now explicitly supplies the limits in the containing-universe category used before passing to its opposite. The restriction equivalence supplies both extension and coherent uniqueness.
- Step 3: read representable-slice density, including its replete full Yoneda image and the canonical coherent cocone. Yoneda full faithfulness identifies this with the category of pairs $(a,y(a)\to X)$ in the item; applying step 2 gives its limit formula. Checked the empty-base case: the extension takes the unique empty presheaf colimit to the terminal infinity category.
- Step 4: read the relative-cone support node against GHN Definitions 9.1/9.15, Propositions 9.12/9.16, Corollary 9.17, and Proposition 10.5's proof. Corrected the claim that the class of all fiber diagrams is itself small. The existing `lem-coef-infinity-limits-products-pullbacks` gives the reduction in the slice of spaces to pushout and small coproduct tests, including the empty coproduct. Wrote the actual locality maps $\operatorname{colim}y_Dr|_B\to y_Dr(\infty)$ and cited Yoneda evaluation and mapping-space colimit/pointwise calculus. Checked both hypotheses of `lem-coef-infinity-reflector-accessibility` by the reflector adjunction, then wrote the inclusion's colimit comparison at a chosen accessibility cardinal $\mu$. The projection's accessibility uses the cited pointwise calculation. These are applications of the cited statements; none is falsely marked elementary.
- Step 5: read cocartesian straightening and its universe clause; applying it to opposites gives Cartesian classification over the large presheaf base in a containing universe. Accessibility passes across the resulting equivalence over the base, since it preserves the colimit universal properties.
- New node `lem-coef-ghn-ind-presheaf-cartesian-realization`: checked each hypothesis, relative cone, edge pullback square, fiber relative-limit condition, and classification against GHN Definition 9.1, Propositions 9.12/9.16 and Corollary 9.17. Its statement contains no proof sketch or accessibility conclusion; it is the separate presheaf realization theorem, not a restatement of the item's accessibility assertion. Added the omitted `def-coef-presentable-infinity-category` statement dependency already cited in its text. Added explicit presheaf and Yoneda definitions rather than incorrectly attributing them to the enhanced-diagram definition; all notions are now defined inline or by listed definition nodes. TeX and source labels checked.
- New node `lem-coef-ind-right-adjoint-coherent`: checked the uniform functor on all small categories with $\lambda$-small colimits against GHN Definition 10.4, including filtered-colimit preservation of its right-adjoint arrows. This is a reusable coherent functoriality theorem, which is not a two-line construction of higher simplices from adjoint existence. Made its extension explicitly the functor $L_u:\operatorname{Ind}_\lambda(C)\to\operatorname{Ind}_\lambda(D)$ of $j_Du$ along $j_C$, so the target and both Yoneda embeddings are unambiguous. Its statement is self-contained, statement-only, and has the correct source and universe/cardinal hypotheses.
- New-node existence searches: independently searched the full shared DAG by relative-cone/Ind/right-adjoint terminology and source numbers, and the whole imported blueprint through the DAG plus the current ancestor proof. The existing presentable-Cartesian-fibration theorem is an ancestor that depends on this item, not a permissible replacement. Neither new statement duplicates a found node. Searched read-only slopmaster2 and upstream master by the item, Ind/presheaf/fibration terms and upstream name table; no exact closed declaration found. Ran fresh LeanFinder, Loogle and Mathlib grep searches with different vocabulary via `msearch.py`; their actual logged results are appended to the new nodes. Returned types concern ordinary categorical stacks, module/representation adjunctions, and unrelated declarations; no infinity-categorical match, hence zero Mathlib leaves.
- Edge cases: checked the terminal base with terminal fiber, identity cocartesian edges, a two-point value at the relative cone point, the empty fiber colimit diagram, a finite coproduct diagram, and $\lambda=\aleph_0$. In particular the empty colimit requires $\phi(0_a)\simeq\phi(-\infty_a)$, not an absolute contractibility assertion. The terminal-fiber example gives total category equivalent to spaces, consistent with the item. The relative-limit formulation and finite-cardinal route pass these tests.
- Changes made: repaired the small test set, wrote its locality maps and reflector/inclusion argument, fixed the cardinal bound, added existing category-limit/Yoneda/pointwise citations with literal quotes, clarified step 1's colimit-preserving extension and both new nodes' presheaf/Yoneda notation, corrected source labels and the stale split summary, added the missing definition dependency, and recorded genuine independent searches. Kept the first worker's `## Review by Q23` and all earlier sections. No new node was added and neither existing new node is elementary, a duplicate, a Mathlib result, or the item's accessibility conclusion.
