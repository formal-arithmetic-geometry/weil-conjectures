# Stage-1 worker report: lem-coef-hammock-inverted-arrow-actions

## Files written

- `dag/nodes/sec-six-functors/lem-coef-hammock-inverted-arrow-actions.json`: existing statement node, now split into five steps; not a Mathlib leaf.
- `citations.json`: verbatim statement quotations for all six step/node citation pairs.
- `report.md`: this author review.

No new nodes, no new definitions, and no Mathlib leaves. The sandbox also contains the search log and source-reading material; these are not DAG delivery files.

## Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id, hammock, inverted arrows, and the weak-equivalence wording did not find a declaration of this theorem. The exact upstream master was also searched as reference material, not as evidence of completion.

## WANTED

WANTED: Dwyer–Kan, *Calculating simplicial localizations*, Definition 2.1 and Proposition 3.3, printed pp.19,21, archival copy under literature/, for lem-coef-hammock-inverted-arrow-actions. The referenced Rochester PDF was read online (a reading copy is in the sandbox); the repository literature was not changed. The proof is marked `proof_origin.by = agent` because Proposition 3.3 states the result after a cancellation observation, without writing out the required prisms. No Stacks tag states the hammock result. No SGA source is used.

## Findings and corrections

The imported statement agrees with Proposition 3.3 and is retained verbatim, including the lack of freeness/calculus-of-fractions assumptions. Its proof was empty. Its single statement dependency does supply exactly the reduced-hammock construction. I retained the original provenance and maintainer-owned unit/chapter binding.

The completed argument is stronger than a bare weak-equivalence assertion: the reverse one-arrow hammock gives inverse maps up to simplicial homotopies with specified orientations. There is deliberately no appeal to the still-unsplit hammock-components theorem or to the free-factor comparison, which uses this item and would be circular. I corrected the potential orientation trap by putting the identity above the cancellation word at x, and below it at y. I reverse continuous time only after realization; there is no simplicial reversal of Delta[1].

For provenance I read both the older blueprint ancestor and the current main-20261015 `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, specifically its second paragraph and displayed derived-coefficient-adjunction calculation. This is a technical input below that calculation through the existing finite-diagram/frame/hammock chain, not a replacement of the unit route. It is not the unit's key node, so no unit realization record is edited.

## Mathlib research

The inherited Mathlib search history is preserved as predecessor provenance. Five additional searches were run through the prescribed msearch command and recorded literally from searches.jsonl in the item: leanfinder for composition with a weak equivalence in hammock localization; Loogle `"hammock"`; grep `hammock|Dwyer.*Kan|inverse.*hammock`; LeanSearch for a homotopy inverse acting on simplicial mapping spaces; and a second leanfinder phrasing using reduced hammocks and reverse zigzags. All services responded. Loogle and grep had no hits. Semantic hits concern model-category homotopy classes, ordinary localizations, chain homotopies, or truncated quasicategory edges. I read Mathlib's ModelCategory/Homotopy.lean around lines 153 and 200: those bijectivity lemmas assume cofibrant/fibrant objects in a model category and concern homotopy classes, not arbitrary reduced-hammock mapping simplicial sets. None is an exact match or one-line specialization.

## Not duplicates

No new nodes are proposed. Whole-DAG keyword searches and whole-blueprint searches for hammock, inverted-arrow weak equivalences, simplicial homotopy equivalence and localization composition found no blueprint node stating this item in another form; `blueprint.same_as` remains empty. Existing realization and homotopy-equivalence tools are cited instead of new elementary cancellation/prism nodes. The existing zigzag-concatenation lemma assumes a natural family of fixed-word equivalences with matching boundary signs; it is not needed for these explicit endpoint cancellation diagrams.

## Review by Q77

I read delivery-errors B through E in full and compared each citation against the actual statement, not its proof. The source read for the item is Dwyer–Kan Definition 2.1 (p.19) and Proposition 3.3 with its preceding cancellation explanation (p.21). There are no new nodes requiring separate source checks.

Step 1 uses the graph-colimit presentation's actual definition: downward W verticals, identity endpoints, negative columns in W, row operators, reduction, and the colimit identification. I checked its quotient/reduction assertion really supplies the normalization relation used to prove that reduction before concatenation makes no difference. Associativity follows by reducing the same concatenation of three diagrams, and the empty word gives the units. This is an explicit calculation from that statement, not a hidden theorem about the hammock localization.

Step 2 again uses precisely the allowable diagrams from the graph-colimit statement. In the x diagram, the middle vertical is u from x in the top row to y in the bottom row, and both endpoint verticals are identities of x. In the y diagram the middle vertical is again u from x to y, with identity endpoint maps of y. In all four squares the two composites are u, by units. Every leftward arrow is either u or an identity, hence is in W, and the only nonidentity vertical is u. The reduced rows are exactly 1_x, ba and ab, 1_y in that order. This verifies every hypothesis with no saturation or Ore property.

Step 3 uses the same row/reduction definition to concatenate e_x or e_y on the target side. At degree n the monotone map [n] to [1] selects the rows of the cancellation diagram; it is not an arbitrary assignment of a top or bottom row. Thus every required vertical exists and points down. Composition respects a simplicial operator by the equality checked in step 1. I checked the four endpoint formulas 1_A, QP, PQ, 1_B, including the source and target of every map. No auxiliary fixed-word comparison theorem is being silently used.

Step 4 gives the other assertion independently at the source end, using the same cited statement and the established row calculation. Its composites are D(ab) and E(ba), not D(ba) or E(ab), which would be ill-typed unless x=y. The homotopy endpoints are Q'P', 1 and 1, P'Q' respectively; the edge direction is not silently reversed.

Step 5 cites two results whose full statements were read. The realization-cylinder node states the natural homeomorphism for every small simplicial set with the ordinary interval product topology and the two endpoint inclusions, exactly what realizes the four simplicial homotopies. Smallness follows because C is small and the diagram shapes are finite, with a set of possible lengths. The homotopy-equivalence-weak node states the component bijection and all based homotopy-group isomorphisms for a pair of continuous homotopy inverses, explicitly allowing homotopies which move basepoints and empty spaces. This is precisely the conclusion required here; I do not assume based homotopies. All quotes in citations.json were checked literally against the cited statements. Both tools are in the item's existing unit, so no off-unit tool declaration is needed.

For small cases I checked the empty category (there is no u, hence the assertion is vacuous), the singleton identity category (all maps and homotopies reduce to identities), an identity arrow at an arbitrary object, a one-arrow category with u distinguished, and a nonidentity endomorphism (the two rows still use different internal objects only when available; for an endomorphism the same square equations remain valid). If an endpoint mapping space is empty, the constructed inverse map forces its partner to be empty too. The continuous homotopy theorem explicitly handles that case. The proof never needs a Kan condition, invertibility of u in C, freeness, or a calculus of fractions.

Against B, there are no unsupported new statements, altered target meanings, or hollow objects; all formulas are single-escaped TeX in the JSON. Against C, the only non-elementary input is the pair of cited realization/topology theorems, and the full cancellation and prism calculations are supplied as elementary steps from the cited graph construction. No proof of a dependency is used as a black box. Against D, the item itself carries both cancellation diagrams and both mapping-space arguments; no clause was moved into a new node. Against E, I checked every W-membership and endpoint type explicitly, particularly the two opposing edge orientations and moving-basepoint issue. The statement needed no correction.

## Unfinished work

None in this one-level split. Server validation is performed by the required --no-push delivery command; its terminal result determines readiness. The sandbox is reserved for the independent second reader, and this worker does not push a delivery.


## Second reading by Q77

- Item statement: checked against Dwyer–Kan, Definition 2.1 and Proposition 3.3 (printed pp. 19, 21) in `source-reading/dk.txt`; the wide-subcategory, arbitrary-object, both mapping-space directions, and no-calculus hypotheses agree. Verdict: PASS.
- Step 1: checked the reduced-hammock definition, row deletion/repetition, reduction, and composition against Definition 2.1, and checked its cited graph-colimit statement supplies these operations. Verdict: PASS; the associativity and simpliciality calculation is elementary from the cited construction.
- Step 2: checked both two-row cancellation hammocks against the displayed hammock conditions and the source proposition; endpoint and middle verticals, leftward W-arrows, square commutativity, and orientations were all type-checked, including identity and endomorphism cases. Verdict: PASS.
- Step 3: checked target concatenation types and the endpoint formulas $1_A,QP,PQ,1_B$ against the graph-colimit statement and the cancellation edges. Verdict: PASS.
- Step 4: checked source concatenation types and the endpoint formulas $Q'P',1_{A'},1_{B'},P'Q'$; in particular the composites are $D(ab)$ and $E(ba)$ with the stated edge orientations. Verdict: PASS.
- Step 5: checked the realization-cylinder and homotopy-equivalence citations verbatim, including endpoint inclusions, moving basepoints, and empty spaces; the conclusion matches the proposition's weak-equivalence meaning. Verdict: PASS.
- New nodes: none; therefore B1–B7 and new-node source checks are vacuous. Whole-DAG and blueprint searches for hammock/inverted-arrow results found no duplicate or blueprint statement, and the recorded Mathlib searches had no exact match. Verdict: PASS.

Changes made during second reading: none to the worker's node, citations, or search log; appended this independent source-and-type audit only. The delivery metadata preserves the existing node's maintainer-owned creation record.
