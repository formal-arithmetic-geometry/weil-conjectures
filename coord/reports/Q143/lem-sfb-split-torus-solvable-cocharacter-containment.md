# Stage-1 worker report: Q143

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-solvable-cocharacter-containment.json`: existing statement, now split in six steps; no Mathlib match.
- `citations.json`: eight step/node entries, with verbatim statement excerpts.
- `searches.jsonl`: seven fresh searches through the required msearch command, retaining their actual results. The item's six inherited Q115 search records are retained as inherited evidence.

No new nodes and no Mathlib leaves. The sandbox also contains the local PDF text extraction and writing script; neither is a delivery node.

## Attachments

None. I searched the whole `lean/WeilConjectures/` tree for the blueprint id and for cocharacter, solvable and Borel terminology. The returned Lie-algebra solvability declarations and trace-formula Borel--Moore terminology do not state this assertion about algebraic subgroup schemes. No finished project declaration gives the item.

## Literature wanted

None for this split. No new nodes require sources. I read the available Milne, Algebraic Groups, iAG2017 PDF through a sandbox text extraction: Definition 17.6 and its dimension observation (pp.353--354), Propositions 21.29 and 21.31, Theorem 21.32 and Corollary 21.33 (pp.433--435), Theorem 12.9 (p.233), the split-case paragraph in the proof of Corollary 12.25 (p.240), Proposition 1.34 and Summary 1.36 (pp.16--17), and the limit-subgroup definitions and Theorem 13.33 (pp.263--266).

## Findings and changes

The imported statement is correct and is unchanged. It deliberately assumes no Borel/maximality condition on V. The geometric Borel containing V must first be chosen; a regular cocharacter chosen arbitrarily need not contain V. I supply the maximum-dimension choice and then apply the converse Borel-description theorem to that particular Borel. Split character antiduality descends its cocharacter, so there is no need to create another node for Corollary 21.33.

The chapter and unit records, three-level rules in SETUP, GOAL, worker brief and delivery-errors B--E were read. I read the latest blueprint's direct-images proof (3) under sec-six-functors-basics/sk-thm-sf-ctf-stability and retained the inherited supporting route. The item has no released repair note. The blueprint ancestor command returns None, consistently with the existing long from.place/from.via record; that record is retained. Whole-blueprint searches for cocharacter, regular cocharacter, Borel and solvable found no equivalent statement. DAG searches by these concepts and Milne 21.29/21.32/21.33 located the existing lemmas used here.

Fresh Mathlib searches used leanfinder twice with different formulations, LeanSearch, Loogle twice, and grep twice (whole Mathlib and AlgebraicGeometry). I read every result: abstract groups' IsSolvable and solvable-subgroup lemmas, Lie Cartan/root-space results, LieAlgebra.Basis.borelUpper/borelLower, and measurable Borel instances. They do not concern the algebraic-group functor P_lambda. Both grep searches had no hits. No unavailable service was treated as a negative result.

## Not duplicates

No new nodes. In particular I reused lem-sfb-regular-cocharacter-borel-description rather than restating Milne 21.32, lem-sfb-multiplicative-character-antiduality rather than creating a split-Hom scalar-extension lemma, and lem-sfb-solvable-normal-subgroup-products rather than a separate Borel-existence node. The two elementary arguments (choosing the largest dimension and descending an affine ideal inclusion) are written as steps, not new nodes.

## Review by Q143

I reviewed all six steps against the actual statements of their cited nodes, rather than their titles or proofs. Every quoted sentence in citations.json was checked as a literal substring of its node statement. All cited nodes belong to the item's unit. A dependency traversal of statement and proof edges from each of the six cited nodes reaches no path back to this item.

Step 1 uses exactly the field-extension clauses of lem-sfb-solvable-normal-subgroup-products (smooth connectedness and solvability persist) and lem-sfb-maximal-torus-field-extension (maximality persists). These statements apply over arbitrary fields. G is already geometrically connected and geometrically reductive by hypothesis; no perfectness assumption is introduced. The affine finite-type conditions are inherited by the closed subgroups involved.

Step 2 uses the strict dimension inequality and boundedness stated in lem-sfb-solvable-normal-subgroup-products. The collection of overgroups is nonempty because V_K is one of them. Its dimensions form a nonempty subset of the finite interval from zero to dim G_K. The maximum therefore exists, and every strictly larger smooth connected solvable subgroup contradicts maximality of dimension. This argument is elementary after the cited dimension result; it uses neither normality of V in G nor an assertion that V itself is Borel.

Step 3 uses the converse clause of lem-sfb-regular-cocharacter-borel-description. The base is algebraically closed, G_K is reductive, T_K maximal, and the chosen B contains T_K, so every hypothesis is available. The node explicitly includes the empty-root case with zero cocharacter and G=T=P(0).

Step 4 uses both full faithfulness of the character antiequivalence and its scalar-extension compatibility in lem-sfb-multiplicative-character-antiduality. They identify Hom(G_m,T) with Hom(X*(T),Z). For split tori the Galois actions are trivial, so every geometric cocharacter descends, even over an imperfect or finite field. The descended map is to the original torus T, not to a conjugate torus. Zero descends to zero.

Step 5 uses the actual coaction-weight and tangent comparison in lem-sfb-relative-tangent-weight-base-change with A=k and B=K; fields are nonzero Noetherian rings and G is smooth affine finite type. A splitting of T supplies its required G_m^r action. This avoids confusing weights of all torus test points with weights tested only on k-rational points (which would fail over finite fields). Extension of a basis proves that a weight summand vanishes before extension exactly when it does afterwards. Character antiduality preserves composition and hence the integer pairing. Regularity over K therefore gives precisely the integers required in the unchanged statement.

Step 6 takes closed representability and field-extension compatibility of P_lambda from lem-sfb-reductive-cocharacter-parabolic-geometry. Its reductivity hypotheses are those of the item. I then wrote out descent on the coordinate rings R/I and R/J: vanishing after tensoring with K is actual vanishing because vector spaces inject into their scalar extensions. This proves the ideal inclusion J subset I, hence a closed subgroup inclusion on every algebra. Merely checking geometric points would not have sufficed, and is not used.

For edge cases I checked a torus G=T (including rank zero and the trivial group), V=T, V a Borel, opposite Borels in SL_2, finite fields, imperfect fields, and nonreduced test algebras. For SL_2 the upper and lower Borels require opposite choices of a regular cocharacter; the proof chooses it from B, as necessary. When Phi is empty the comparison in step 5 makes the geometric root set empty, so step 3 and descent give lambda=0. There is no characteristic-zero Lie-algebra argument, extra separability assumption, weakened conclusion or statement dispute.

Against delivery-errors B--E: there are no new unsplit nodes with hidden proofs, duplicated facts or missing notion definitions; all existing metadata and the statement are retained. No lemma is a relabelled clause. Every non-elementary fact is attached to a cited statement; the dimension choice and ideal descent are explicit routine arguments. All steps are shorter than 2000 characters, so there is no long step hiding another lemma. No SGA source or forbidden route was used. I found nothing unfinished mathematically in this split; the existing cited lemmas remain their own stage-1 items where appropriate.

## Unfinished work

None in the assigned split. Delivery verification follows this report.
