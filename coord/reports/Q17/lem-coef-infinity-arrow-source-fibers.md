# Stage-1 split: lem-coef-infinity-arrow-source-fibers

Group Q17; 2026-10-17 (local date; the logged search timestamps are UTC on 2026-10-16).

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-arrow-source-fibers.json`: statement, split into six proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-cocartesian-mapping-criterion.json`: statement-only, unsplit; no Mathlib match. This is the generic equivalence between the relative outer-horn criterion and the homotopy pullback criterion on mapping spaces, not an arrow-category assertion.
- `dag/nodes/sec-six-functors/lem-coef-infinity-isofibration-pullback-limit.json`: statement-only, unsplit; no Mathlib match. This concerns every isofibration between quasicategories, with its universal property tested on cores of functor categories.
- `citations.json`: one verbatim quotation for each cited node in each numbered step.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item tag, source fibers, cocartesian/coCartesian, quasicategory, and isofibration found no declaration of this item or either new statement. The master reference checkout likewise supplied no coherent source-fibration declaration. No compiler, Lake, or build was run.

## WANTED

WANTED: Lurie, Higher Topos Theory, Proposition 2.4.4.3 and proof of Lemma 5.5.5.14, for `lem-coef-infinity-arrow-source-fibers` and `lem-coef-infinity-cocartesian-mapping-criterion`; read the Harvard-hosted PDF online, but it is not archived under literature/.

WANTED: Kerodon, Corollary 4.5.3.28 (Tag 033R), Corollary 4.5.3.29 (033T), and Proposition 4.5.3.15 (033C), for `lem-coef-infinity-isofibration-pullback-limit`; all read online. These are Kerodon tags, not Stacks tags. No Stacks tag states either new quasicategorical theorem.

## Problems found and corrected

The statement is unchanged and is not disputed. Its source's terse first paragraph did not expose either the coherent mapping-space calculation for the pushout lift or the general theorem identifying a strict fiber with a categorical homotopy fiber. The split now writes the pushout argument in the item's steps and cites the general infrastructure separately.

During self-review I removed a preliminary use of `lem-coef-infinity-pointwise-cocartesian-transport` to pass from its mapping-space convention to this item's horn convention. That node states exponentiation and transport after defining cocartesian edges by their mapping-space property; its statement does not explicitly assert equivalence with the relative horn convention in `def-coef-infinity-fibrations`. The new generic criterion makes that implication an exact citation. This avoids treating the source list of an existing node as though it were part of its statement.

The archived main-20261015 proof of `prop-coef-integral-exceptional-adjoint`, paragraph 2 (the finite-coefficient mapping-complex adjunction before the displayed derived limit), and the chapter/unit records were read. This node supplies foundational coherent category infrastructure reached through the existing presentable-adjoint chain; it does not replace a geometric step of the unit. It is not a unit key node, so no unit realization fields were changed. The generic cone calculus is declared in `split_report.tool_uses` because it belongs to another unit. No SGA source is used.

## Unfinished work

The two new lemmas are intentionally statement-only stage-1 queue entries. Nothing in the requested one-level split is left as an unsupported step. No Lean was written. No delivery push was made; the accepted sandbox is for the second reader.

## Not duplicates

`lem-coef-infinity-cocartesian-mapping-criterion` vs `lem-coef-infinity-pointwise-cocartesian-transport`: the existing node defines its cocartesian edges by mapping spaces and proves functor-category transport; the new node explicitly equates that property with the horn criterion for an arbitrary inner fibration, without assuming existence of other lifts.

`lem-coef-infinity-cocartesian-mapping-criterion` vs `lem-coef-infinity-grothendieck-limits-colimits`: the existing node defines cartesian/cocartesian fibrations by mapping spaces and proves a total-category colimit formula; it does not state the horn/mapping equivalence.

`lem-coef-infinity-isofibration-pullback-limit` vs `lem-coef-infinity-isofibration-base-change`: the existing node concerns invariance of strict pullbacks of an equivalence between two isofibrations over the same base; it does not state the categorical pullback universal property for one arbitrary isofibration.

`lem-coef-infinity-isofibration-pullback-limit` vs `lem-coef-accessible-infinity-pullback`: the existing node proves accessibility of a homotopy pullback of accessible functors; it does not identify a degreewise simplicial pullback with that homotopy pullback, and its accessibility assumptions are absent here.

`lem-coef-infinity-isofibration-pullback-limit` vs `lem-coef-infinity-mapping-excision`: excision computes mapping spaces in functor categories on a glued indexing shape, not arbitrary categorical pullbacks of isofibrations.

The whole DAG, including all chapters, and the imported blueprint were searched before making either new node. Blueprint searches for cocartesian, isofibration, source evaluation, homotopy pullback, categorical pullback, mapping-space, the relevant theorem numbers and Kerodon tags found no blueprint node stating these facts. Searches for the theorem numbers in DAG node source fields found the related nodes above; their statements were opened. No existing node has Kerodon Tag 033R in its source. No new node is a clause of the arrow-specific item: its proof computes the pushout mapping squares explicitly instead of applying a renamed source-fiber lemma.

## Review by Q17

I read the online HTT proof of Lemma 5.5.5.14 on printed p. 491, which uses the full arrow subcategory, pushout stability and its fiber square. I also read Proposition 2.4.4.3 on printed p. 131 for the mapping-space criterion, and Corollary 3.3.1.4 on printed p. 206 for the categorical homotopy pullback issue. For the new pullback node I read Kerodon 033R, 033T and Proposition 4.5.3.15: the last tests the whole universal property on cores of functor categories, so the conclusion is a pullback in Cat-infinity, not a pullback after discarding noninvertible arrows. For the generic criterion I checked the opposite of HTT Proposition 2.4.4.3 against the horn-based definition already in the DAG. Its hypothesis is only an inner fibration between quasicategories; no other cocartesian lifts are assumed.

For Step 1 I opened `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-isofibration-exponentiation`, and `def-cbc-enhanced-diagrams-cones`. The first explicitly gives quasicategories for the functor category and full subcategory; the second explicitly gives an isofibration for restriction along any monomorphism. I checked that {0} to Delta-1 is degreewise injective. An inner-horn filler has the same vertices, so it lies in the full subcategory. Repleteness is used precisely when lifting an equivalence, and the inverse witnesses also lie in the full subcategory. This checks the isofibration hypothesis needed later, without assuming that evaluation is a Kan fibration.

For Step 2 I opened the cone calculus, mapping excision and arrow-morphism-square statements. The cone calculus explicitly has the dual colimit criterion. Excision explicitly allows a pushout of indexing simplicial sets along a monomorphism. Two intervals sharing their source have exactly this form. The arrow formula applied to a constant target identifies the two transformation spaces with the two target-vertex mapping spaces. Thus their homotopy pullback, including the path on the overlap, is the space of coherent cocones. This supplies the pushout mapping formula; no unquoted theorem on pushout mapping spaces is being borrowed. The chosen pushout exists by the hypothesis on C, and stability under pushouts places its new bottom arrow in P.

For Step 3 I opened the arrow-morphism-square formula again and checked its naturality and endpoint-projection clauses, not only its bare equivalence. The test object is an arbitrary arrow h:T to Z in P, so the full subcategory mapping spaces are exactly the ambient ones. I also opened `lem-coef-kan-homotopy-pullback-invariance`: it explicitly permits replacing the mapping-space corner by an equivalence. The Step 2 equivalence has the stated restriction maps. After substitution the intermediate path datum can be concatenated away; the inverse homotopy shortens the path with variable endpoint. This leaves the same map a-prime and b and the same compatibility path on both sides, including its higher homotopies. The resulting comparison is the precomposition map for the actual pushout square, by the naturality clause, not just an unrelated equivalence of spaces. The new criterion's exact statement supplies its interpretation as a cocartesian edge in Step 4. I removed the preliminary ambiguous transport citation as described above.

For Step 4 I checked that the new criterion's inner-fibration hypothesis was established in Step 1 and that Step 3 ranges over every vertex of the total category. Step 2 supplies the required lift for every base arrow and every source. The definition node, which I opened, then applies literally; it is cited only for this final assembly of the fibration definition, not for the non-elementary mapping/horn theorem.

For Step 5 I checked E=A_P, B=C, T=Delta-0 and g=X against every hypothesis of the new pullback node. Both total and base are quasicategories by Step 1 and p is an isofibration there. Delta-0 is a quasicategory. The fixed universe is large enough for the entire input; Cat-infinity is formed in the next universe. No smallness of C in a smaller colimit universe, accessibility, presentability, or nonempty fiber is needed.

For Step 6 I checked the full-subcategory and internal-functor definitions degree by degree. The source restriction is the entire constant X simplex, not just its vertices. The P condition is a condition on the vertex arrows only. Thus the identification is of simplicial sets with the same operators, and every triangle homotopy and higher compatibility is retained. This is the only elementary-only proof step; it creates no lemma node.

I tested the new statements and the split on empty total categories and empty fibers, the identity fibration, a map to a point, and nerves of ordinary categories. For P empty the lift assertion is vacuous and the fibers are empty; no proof step picks an object. For P all arrows the construction is ordinary pushout transport. For P equivalences the bottom arrow of a pushout is again an equivalence. In ordinary category nerves the new criterion reduces to the usual universal mapping square and the isofibration pullback theorem reduces to the equivalence between a strict and an iso-comma pullback. Omitting equivalence lifting would fail: the inclusion of one object in a two-object connected groupoid, pulled back at the other object, has empty strict fiber but nonempty categorical homotopy fiber. Thus repleteness and isofibration have not been dropped where they are needed.

I checked delivery-errors B through E: new statements introduce all objects and notions with definition dependencies; they have no proof or proof dependencies; they are not elementary observations, duplicates or restated clauses; their searches ran through msearch.py and the exact records were copied from searches.jsonl. The hits were read: ordinary IsCocartesian uses Hom sets; QCat.strictBicategory gives a homotopy bicategory; innerFibration_pullbackObjObjπ only gives an inner-fibration property; the categorical-pullback file has ordinary Category instances. None states either coherent theorem. The new statements received two semantic phrasings, Loogle and grep, plus LeanSearch. All services succeeded. Citations were checked as literal substrings of the cited statements, and proof_deps is exactly the union of step uses. I made no source-statement correction and added no hypothesis.

## Second reading by Q17

- Item statement: checked against HTT Lemma 5.5.5.14, first paragraph (PDF pp. 491–492), Proposition 3.3.1.3 and Corollary 3.3.1.4, and Kerodon 033R; every hypothesis (quasicategory, pushouts, pushout-stability, repleteness, universe) and both cocartesian-fibration and strict-fiber clauses agree; verdict PASS.
- Step 1: checked against `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-isofibration-exponentiation`, `def-cbc-enhanced-diagrams-cones`, and Kerodon 01F3; full-subcategory horn filling and equivalence lifting use exactly the cited statements; verdict PASS.
- Step 2: checked against `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-mapping-excision`, `lem-coef-infinity-arrow-morphism-square`, and HTT Lemma 5.5.5.13; the two-interval simplicial pushout and all restriction maps reproduce the coherent pushout mapping-space formula; verdict PASS.
- Step 3: checked against `lem-coef-infinity-arrow-morphism-square`, `lem-coef-kan-homotopy-pullback-invariance`, `lem-coef-infinity-cocartesian-mapping-criterion`, and the full-subcategory clause of `def-cbc-enhanced-diagrams-cones`; path elimination retains the higher compatibility data and gives the actual precomposition map; verdict PASS.
- Step 4: checked against `lem-coef-infinity-cocartesian-mapping-criterion` and `def-coef-infinity-fibrations`; Step 1 supplies the inner fibration and Step 2 supplies every required lift, so the definition applies literally; verdict PASS.
- Step 5: checked against `lem-coef-infinity-isofibration-pullback-limit` (Kerodon 033R/033T and Proposition 4.5.3.15); the source-evaluation isofibration and point functor satisfy the stated hypotheses, with no hidden fibration, accessibility, or nonemptiness assumption; verdict PASS.
- Step 6: checked against `def-cbc-enhanced-diagrams-cones` and the explicit degreewise definition of coherent functors; the fiber is exactly the full coherent coslice subcategory on P, including triangle homotopies and higher simplices; verdict PASS.
- New node `lem-coef-infinity-cocartesian-mapping-criterion`: statement-only and self-contained with definition dependencies; checked against HTT Proposition 2.4.4.3 (dual) and its horn characterization; tested on identity, empty, and ordinary-category nerve cases; verdict PASS.
- New node `lem-coef-infinity-isofibration-pullback-limit`: statement-only and self-contained with definition dependencies; checked against Kerodon 033R, 033T, and Proposition 4.5.3.15; tested on identity, empty, point, and ordinary-category nerve cases; verdict PASS.

Changes made in this second reading: none. The worker’s six-step proof, two statement-only infrastructure nodes, citations, Mathlib search log, duplicate analysis, blueprint references, and edge-case checks were all retained because they matched the opened statements and sources. No source statement was disputed or corrected, no Lean or build tool was run, and no SGA source was introduced.
