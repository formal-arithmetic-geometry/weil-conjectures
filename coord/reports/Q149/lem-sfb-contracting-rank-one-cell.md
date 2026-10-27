# Q149: lem-sfb-contracting-rank-one-cell

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-contracting-rank-one-cell.json: statement retained; split into nine proof steps. Mathlib verdict: no match. No new nodes and no Mathlib leaves.
- citations.json: one entry for every step/node citation, with the full verbatim cited statement so that every clause taken from it is available.
- searches.jsonl: actual search-command results; the preexisting item's search history is retained in its JSON. Scratch sources and the writing script are confined to this sandbox.

## Attachments

None. Searched the live project under lean/WeilConjectures for the item id, contracting/cocharacter, mixed-commuting and root-subgroup language. Matrix rank-one and Weil-character rank-one declarations do not concern this item. No sorry-free project declaration states it.

## Sources and searches

Read Milne, Algebraic Groups (2017), Section 2h, printed pp.54--56 (especially Propositions 2.46--2.48), Theorem 13.33 and its matrix proof, pp.265--266, Theorem 21.11 and its proof, pp.428--430, and 23.21--23.23, pp.491--492. Read Theorem 23.31, p.494: Milne refers its proof out to Steinberg. This split does not invoke Theorem 23.31, whose generation conclusion is the parent of our item. Instead it realizes the explicit closure/word induction of 23.22 and the general cocharacter chart of 13.33. The explicit Gauss calculation supplies the rank-one replacement used in that induction. No SGA source is used.

WANTED: Steinberg 1999, 5.4 and 5.6--5.10, for the external reference in the inherited source of lem-sfb-contracting-rank-one-cell; not an input to this delivery's proof.

Read the chapter and unit records, SETUP's three levels and GOAL. Read the current blueprint under literature/blueprint/latest (current ef6f9619), including its direct-images alteration branch. The supporting algebraic-group chain and the unit are retained. The blueprint ancestor tool returns None for this supporting item, consistently with its inherited from.node=null; the existing provenance is retained. Blueprint searches for cocharacter, big cell, generated subgroup, subgroups generate and multiplication words gave no matching imported node; triangular and rank-one searches gave unrelated sheaf/Lie-algebra nodes. Whole-DAG statement/title searches found the existing general inputs below, so none was duplicated.

Ran actual msearch commands for leanfinder, loogle, grep and leansearch. The item search and a second phrasing about smooth generated subgroups returned abstract/topological groups, CW cells or abstract Lie-module triangularizability. Read the printed hits: none states a group-scheme multiplication-cell theorem or the scheme-theoretic root-generation argument. The AlgebraicGeometry grep for cocharacter|root.subgroup|big.cell had no hits. All new recorded query texts are taken directly from searches.jsonl; there were no unavailable services. No new-node Mathlib classification is needed.

## What was wrong or incomplete

The statement requires no correction and the item has no repair note. Its proof was empty. In particular, it would be circular to use the parent's reductivity theorem or a reductive big-cell theorem on G. The proof below uses only reductivity of the supplied J_alpha. The parent was not cited, and traversal of every proposed dependency found no return path to this item.

A Gauss formula alone only works on 1+ab nonzero; step 6 treats its zero locus by pulling equations back to an affine parameter space and using injectivity of localization in a polynomial domain. Rational density alone also does not identify nonreduced subgroup schemes; step 8 makes the smaller product a closed subscheme of the smooth cocharacter chart and uses reducedness there to prove scheme equality.

## Not duplicates

No new nodes. The reused cocharacter structure statement omits openness from its statement, even though its proof establishes it: step 1 therefore separately cites the existing transverse-subgroup-product-open statement. The root-generation statement for an already reductive group would not apply to G; instead the tangent-generation statement is applied separately to each reductive J_alpha, after reading its two-root Lie decomposition.

## Review by Q149

I checked delivery-errors B--E against the actual statements, not their titles. There are no new nodes to audit for missing notions or hidden proof text, no newly asserted Mathlib match, and no change in any target or definition. I read all cited node statements in full; citations.json copies them verbatim. Existing definitions in the item already introduce the field, group schemes, closed subgroups, smoothness, connectedness, finite type and root parametrizations.

Step 1 uses cocharacter-limit-smooth-structure for smoothness, connectedness, unipotence, semidirect products and precisely the Lie-weight formulas in its statement. It does not take openness from that node's proof. Central-torus-faithful-weight-blocks permits T=1 and gives a closed faithful embedding; gm-representation-weight-basis gives a basis valid on all algebras. The entry computation proves the functor intersections. Transverse-subgroup-product-open then applies with H=U_- and K=P_+: both are smooth closed subgroups, their scheme-theoretic intersection is trivial and their Lie spaces are complementary. Reordering the supplied semidirect product gives the three-factor chart.

Step 2 uses reductive-root-subgroup-parametrizations on each J_alpha, which is reductive with the stated maximal torus, not on G. Its conjugation equation gives the exponents +n and -n. The palindromic multiplication parameter has inverse-stable image on every algebra and contains the identity; its affine-space source is geometrically integral. These verify every hypothesis of affine-pointed-map-generated-subgroup. Its conclusion gives reducedness and connectedness; geometrically-reduced-group-smooth then applies because the subgroup is finite type. Unipotence is inherited from the containing cocharacter kernels with the same faithful representations.

Step 3 uses the actual intersection-of-kernels formula in affine-pointed-map-generated-subgroup. Nullstellensatz-vanishing applies to polynomial/Laurent polynomial coordinate domains over the algebraically closed F. The two-root Lie decomposition and root tangent lines are supplied by reductive-rank-one-reflections and reductive-root-subgroup-parametrizations. Smooth-subgroup-tangent-generation is applied to T and the two root groups inside each smooth connected J_alpha. It allows the putative containing subgroup to be nonsmooth. These facts justify generation by all signed root groups and T before the same explicit ideal argument proves schematic density of Gamma. This step does not confuse generation as a closed subgroup with equality of abstract rational-point groups.

Step 4 derives torus normalization on universal word maps, hence on the defining ideal; coefficient comparison in the free Laurent monomial basis justifies passage to its intersection. The closure's left V and T stability is then translation of the defining product. Step 5 uses opposite-root-sl2-parametrizations, whose statement supplies both upper and lower isomorphisms and the diagonal coroot identity. Its matrix calculation is written out, so no rank-one decomposition theorem is hidden. This input is also used only on J_alpha.

Step 6 is the source's induction with its base, distinct-root case, equal-root case and exceptional locus all present. The nonzero polynomial 1+ab is not replaced by an invertibility assumption on all points. Nullstellensatz is applied on its reduced principal affine open, then the polynomial-domain localization is injective. Step 7 uses only the densities and stability already proved in steps 3--6. In review I made right T stability explicit, as well as right U stability, before concluding uV T U is in the closure. The conclusion C=G follows from schematic density of Gamma, not an unproved pointwise generation claim.

Step 8 identifies the product as a closed subscheme of the already constructed open chart, rather than assuming the product is closed in G. Smooth-geometrically-reduced is applied to G over Spec F; its only fibre is G. A closed subscheme supported everywhere in a reduced scheme has zero defining ideal (elements lie in the nilradical). Coordinate-axis pullbacks then give U=U_+, V=U_- and T=Z as schemes, so all clauses include nonreduced test algebras. Step 9 uses the semidirect-product statement to identify TU and TV as the closed limit-exists groups, and the unipotent-solvability statement supplies finite normal series with commutative quotients. The elementary derived-series argument is written out to match exactly the item's definition of solvable.

Small cases checked: D with one root, SL_2 and PGL_2 in characteristic two, central torus factors not spanned by D, a nonprimitive character and pairings n divisible by the characteristic, the locus 1+ab=0, and arbitrary nonreduced coefficient algebras in the block-intersection argument. All weights are characters, never their differentials, so these cases introduce no characteristic-zero premise. D nonempty excludes the torus-only case, but the coordinate-chart argument would handle it too. No proof step exceeds 2000 characters. No new lemma is hidden in a long step: the generation construction is an application of the existing coordinate-ideal theorem, the main word induction is explicit, and the cell equality is a direct closed-immersion argument.

Generic off-unit tools declared in split_report.tool_uses: lem-wf-affine-nullstellensatz-vanishing for polynomial equations on word spaces, and sbc-lem-smooth-geometrically-reduced for reducedness of the smooth chart. Neither replaces a step of the unit's alteration route.

## Unfinished work

None within this stage-1 item. No Lean was written and no compiler, Lake or build tool was run. New nodes: 0; Mathlib leaves: 0. Required server dry run and delivery follow this self-review.

Dry-run repair: the first preflight treated the legitimate TeX matrix row separator in step 5 as doubled command escaping (B4). Rewrote the matrix by its four row-ordered entries; the formula and proof are unchanged.
