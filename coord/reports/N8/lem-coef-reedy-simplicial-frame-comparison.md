## Worker report

Files written:
- `dag/nodes/sec-six-functors/lem-coef-reedy-simplicial-frame-comparison.json`: item, statement, split; complete proof in four steps. Not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `searches.jsonl`: actual search-command results for the item, retained unchanged.
- `report.md`: this report and the direct-delivery review.

## New nodes

None. Zero new Mathlib leaves; the proof reuses the existing Mathlib leaf `lem-weil-pbc-left-adjoint-preserves-colimits` and the existing `lem-coef-reedy-model-structure`.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, Reedy, simplicial frames and left Quillen terminology found no declaration stating the item. The analogous master search also found none; master is reference material only.

## Sources and wanted material

WANTED: Mark Hovey, *Model Categories*, Definitions 5.2.1–5.2.2, Theorem 5.2.5, Theorem 5.2.8 and Lemma 5.5.1, for lem-coef-reedy-simplicial-frame-comparison. The book is not archived under literature/. I read the existing source URL online, https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf, particularly printed pp.124–128 and 133 (PDF pages 133–137 and 142). No download or literature edit was made. The proof is marked agent because the local source collection lacks the book and the transport argument is supplied explicitly. Hovey 5.2.5 gives the exact relative-latching trivial-cofibration criterion and diagram-category lifting axiom. The dual construction of 5.5.1 explains the frame comparison. The broad inherited reference to 5.4.7 concerns mapping complexes; it is not invoked as a black box here.

I also read `literature/stacks-project/categories.tex`, `lemma-adjoint-exact`, Stacks tag 0038, part (1) and proof, lines 3472 onward. This is the actual source of the existing left-adjoint-colimit node. No Stacks tag states the frame comparison, and none has been invented. No SGA source is used.

## Blueprint and existing-node searches

Read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, and the main-20261015 ancestor statement and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint{,.proof}.md`. Paragraph 2 is the displayed derived coefficient adjunction. The item retains its existing ancestry via the frame-mapping lemmas. It is not the unit's key node, so there is no unit edit.

`tools/blueprint_refs.py ancestor lem-coef-reedy-simplicial-frame-comparison` identifies prop-coef-integral-exceptional-adjoint. Whole-blueprint searches for `Reedy` and `simplicial frame` returned zero matching blueprint nodes. The whole-blueprint `adjoint colimit` search returned eleven nodes, all more specific constructions rather than the present comparison. Whole-DAG searches for Reedy/frame terminology and for left-adjoint colimit preservation led to the two reused dependencies. I read their full statements, and the statements of `lem-coef-reedy-left-frame-comparison`, `lem-coef-cosimplicial-frame-mapping`, `def-weil-pbc-category-colimit` and `lem-coef-lifting-class-closure`, before deciding no new node was justified. The left-frame comparison concerns augmented cosimplicial frames and is not a duplicate of this coaugmented simplicial statement. The parent frame-mapping theorem is not cited, which avoids introducing a cycle.

The left-adjoint preservation node is a generic Mathlib tool, hence admissible across units. Its exact statement covers every small latching index and the pushout span; it is not restricted to filtered colimits. Its pinned declaration is `CategoryTheory.Adjunction.leftAdjoint_preservesColimits` in Mathlib/CategoryTheory/Adjunction/Limits.lean, line 92, read in the pinned checkout. The Reedy dependency is in this item's own unit.

## Mathlib audit

All new searches were executed with the required `msearch.py N8 lem-coef-reedy-simplicial-frame-comparison` command, and their actual log records are appended to the item's inherited search history. I used LeanFinder with two distinct phrasings, LeanSearch, Loogle with `"Reedy"` and `HomotopicalAlgebra.ReedyStructure`, and grep in both AlgebraicTopology and CategoryTheory. The inherited search records are preserved, not represented as newly executed searches.

The hits are ground-model weak factorization systems and lifting lemmas, horn lifting in simplicial sets, the combinatorial ReedyStructure, and localization of cofibrant objects. I read the pinned Mathlib/AlgebraicTopology/Reedy/Basic.lean; lines 21–24 explicitly list the Reedy model structure on functor categories as a TODO, while its structure at lines 38–54 only defines the indexing category. These hits do not give the present transported-frame comparison. The general colimit-preservation declaration is already the existing Mathlib leaf, so I cite that leaf instead of creating another node.

## Problems found and corrections

The initial item is a statement-only node, not an existing failed split. Its statement is correct with all the stated hypotheses, and it is preserved verbatim. No STATEMENT-DISPUTED correction is needed. The proof now makes explicit what cannot be inferred merely from the title: a left Quillen functor need not preserve Reedy fibrant objects or arbitrary weak equivalences. It instead preserves this *Reedy trivial cofibration* by its relative latching formula. The comparison uses fibrancy of the target diagram B', and its exact lift equation forces the specified endpoint without a separate relative-degree-zero extension theorem. Neither Brown's lemma nor a new frame-transport lemma is needed. The inherited searches' broad no-match explanations are retained as historical imported data; the new verdicts describe the actual present question.

## Not duplicates

No new nodes, hence no new/existing pairs. Every added mathematical input is already a cited DAG statement.

## Unfinished

Nothing in the requested split is left unfinished. The delivery gates and push are recorded below after running them.

## Review by N8

I read the actual item, both cited statements, the relevant Hovey pages online, Stacks 0038 locally and the current ancestor proof before signing this split. Hovey 5.2.5 permits the same model-category hypotheses as the item, including functorial factorizations; the small index is Delta-op. This item is a derived application of that theorem, rather than a restatement of all its content. No source supplies an extra properness, simplicial enrichment or combinatorial hypothesis, and the proof uses none.

Step 1 cites `lem-weil-pbc-left-adjoint-preserves-colimits` for image colimit cocones, not just abstract existence, and `lem-coef-reedy-model-structure` for the precise latching index and relative-latching map. Its three isomorphisms apply preservation twice to latching colimits and once to a span pushout. Checking the two pushout restrictions explicitly identifies the arrow, so this is a routine substitution in cited formulas, legitimately elementary. The smallness hypothesis is verified using the slice of the small simplex category; at degree zero the empty colimit is included. There is no unstated commutation of T with a limit.

Step 2 uses the Reedy node's *trivial* relative-latching characterization in both categories, not merely its ordinary cofibration clause. The item itself assumes T preserves trivial cofibrations. Applying that assumption to the latching map gives the result, and the same Reedy statement explicitly identifies weak equivalences objectwise. Thus the use of T(i_n) as a weak equivalence later does not require Brown's lemma, nor objectwise cofibrancy assumptions. The deduction is elementary from the cited criterion.

Step 3 uses the Reedy node's assertion of a model structure and its explicit mutually characterized diagonal-lifting classes. The terminal arrow of B' is a fibration exactly by assumed Reedy fibrancy. T(i) is the trivial cofibration just proved, and the displayed square commutes by terminal uniqueness. The lift is in the functor category, which proves naturality rather than merely choosing unrelated degreewise lifts. This is the only step marked non-elementary, and its complete lifting theorem is the statement of the node it cites. I checked that the quoted WFS sentence is verbatim and not an inference from a proof hidden in the dependency.

Step 4 uses the degree-zero identities from the item's hypotheses and the two-out-of-three clause of the Reedy node, first for the composite i'_n r and then to cancel T(i_n) from the equation. The item does not require i' itself to be a Reedy cofibration, so no such assumption is used. r being a trivial cofibration supplies its weak equivalence; Z's fibrancy and Y_c's bifibrancy are compatible retained hypotheses, though the stated comparison actually needs only the given diagrams, their coaugmentations and the weak equivalence r.

For small cases I tested n=0 explicitly: the relative latching objects are initial and T preserves them; the lift equation gives b_0=r exactly. For n=1, the Delta-op latching object is the degree-zero object, not the two-fold coproduct that belongs to Delta; the proof uses the general slice formula and hence the correct variance. With T the identity, r the identity and B=B' the construction allows b to be the identity. With different B and B' it still uses only the stated coaugmentation equations. Arbitrary n uses exactly the same pushout universal property, without a connectedness or nonempty-latching assumption. I introduced no new statements requiring additional edge-case tests.

Against delivery-errors B–E: no new nodes with hidden proofs or missing definitions; no relabelled clauses, duplicate nodes or unsearched leaves; every cited node was opened and provides exactly the assertion used; citations.json has each step/node pair with a verbatim substring; the only imported definition dependency already defines all the model/Reedy notions; no off-route theorem, no parent citation, no SGA, and no silent statement change. Every proof step has fewer than 2000 characters (1051, 639, 807, 617), and none hides a separate general comparison lemma. I corrected the previously absent proof by the four arguments above; no changes were requested by a second worker because this is the explicitly authorized direct-delivery workflow.
