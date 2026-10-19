# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-contravariant-fibrations-between-right-fibrations.json`: statement, split into six proof steps; not a Mathlib match. No new nodes and no Mathlib leaves.
- `citations.json`: fourteen entries, one verbatim statement passage for every step/node pair.
- `searches.jsonl`: actual results recorded by msearch.py; inherited searches in the repository node were retained, and this worker's five item searches appended to its mathlib_searches.
- `report.md`: this handover and self-review.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id and by contravariant-model, right-fibration and right-anodyne terminology; there is no project declaration stating the item. The upstream-master reference search also found no such result; no master sorry declaration was treated as a proof.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, Corollary 2.2.3.14 and its proof, printed pp. 86–87, for lem-coef-contravariant-fibrations-between-right-fibrations. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf (PDF zero-based pages 103–104); no local archival copy exists in literature/. No download was made. The fully expanded proof is marked proof_origin.by = agent, as the brief requires for literature not archived locally.

## Findings and corrections

The existing statement is correct and unchanged, including its arbitrary simplicial base, universe convention, and both directions. The node previously had no proof. Its source's proof is the route used here: factor in the contravariant model, compare fibers first over S and then over Y, obtain a homotopy inverse over Y, and correct a provisional lift by the endpoint cylinder. The source's reference to a “covariant fibration” in the last paragraph is a harmless word error: that paragraph explicitly tests trivial cofibrations in the contravariant model. The delivered proof consistently uses the contravariant model. This is not a statement dispute.

The important citation issue was the fiber comparison: right properness alone does not directly identify the map on the fibers of a map between two fibrations. The existing `lem-coef-kan-fibration-arbitrary-base-fibers` states exactly the required implication and is cited. Thus no new comparison lemma was created. Likewise, the existing presentation theorem supplies both the fiber criterion in RFib(Y) and the Kan property of its mapping spaces; no mere definition is cited for those theorems.

Read the chapter/unit records and the ancestor in both the current main-20261015 blueprint and the older master location. The item is a supporting model-category argument for the presentable Cartesian-fibration construction in the recorded ancestor place. It is not a unit's key statement; neither chapter nor unit was edited. Its inherited chapter/unit metadata was retained. No route was replaced. `lem-cbc-right-fibration-space-fiber` is declared in split_report.tool_uses as the generic off-unit horn-comparison theorem needed for Kan vertex fibers; it does not replace a geometric step of the unit.

## What remains unfinished

Nothing in this one-level split. The fresh second reader must inspect the split and deliver it. This worker runs only --no-push and does not deliver. No Lean was written or compiled, and no live source, repository, launcher or coordination file was changed.

## Not duplicates

No new nodes. Whole-DAG searches for contravariant-model and right-anodyne terminology, followed by reading the candidate statements, found all the inputs already present. Blueprint-reference searches for “contravariant”, “contravariant fibration”, “right fibration” and “Kan fibration” produced no blueprint node stating this supporting lemma. The existing created-node ancestor was confirmed by blueprint_refs.py ancestor. The item's same_as remains empty and its already-specific from.place is retained.

## Review by Q42

I read HTT Corollary 2.2.3.14, including the factorization argument on printed p. 86 and the homotopy-extension diagram on p. 87, and the adjacent Corollaries 2.2.3.12–13 on the same online pages. Its objects are arbitrary simplicial sets, and both structure maps are right fibrations. These are exactly the item's hypotheses. In particular I did not promote the base S to a quasicategory or a Kan complex. There are no new-node sources to check.

For Step 1, I opened def-coef-infinity-right-anodyne, lem-coef-contravariant-slice-model and def-coef-infinity-fibrations. The first includes every positive right horn, the second explicitly makes every right-anodyne map a trivial cofibration over any base and characterizes model fibrations by lifting, and the third defines right fibrations by those same horns. Composing the bottom map to S makes an ordinary horn square a slice square, so the lift has exactly the required base map. This also proves the forward implication for the later map q without assuming the result being proved.

For Step 2, the slice-model statement supplies model factorizations, the exact fibrant-object characterization, Kan vertex fibers, and the weak-equivalence criterion for maps between right fibrations. I used its trivial-cofibration/fibration factorization; i is therefore a weak equivalence. Step 1 applies to q. Composition of the two right fibrations is written as two successive horn lifts using the definition, not assumed as an uncited theorem. Hence all three fibers X_s, X'_s, Y_s really are Kan, and the cited fiber criterion does give weak i_s.

For Step 3, I opened lem-cbc-right-fibration-space-fiber and lem-coef-kan-fibration-arbitrary-base-fibers. The former explicitly requires a Kan base and turns a right fibration into a Kan fibration; the only base to which I apply it is Y_s, already Kan. The latter states the if-and-only-if for a map between two Kan fibrations over a common base and includes empty fibers. Applying its forward implication to i_s gives the maps on fibers over y. The equality between those fibers and X_y,X'_y is checked degree by degree in the step. Pullback preservation of right-horn lifts is also written out, so this step uses no unstated base-change theorem. The input is the statement of each cited node, not its proof.

For Step 4, I read the whole statement of lem-coef-simplicial-right-fibration-presentation. Its equivalence criterion is for any simplicial base, not just quasicategories, and its equivalence means an actual simplicial homotopy inverse. Its separate Kan mapping-space clause permits reversing the homotopy edge. I wrote out the two specified edges of the 2-horn that reverses it. The inverse and the homotopy are over Y, which is essential: having them only over S would not let the subsequent endpoint correction solve the original square.

For Step 5, the slice-model's fibration condition gives e with both ej=ia and qe=b. The formulas e'=ge and h(a × 1) agree at the endpoint because e'j=gia; their images in Y are b and bj, respectively. These are direct equations from earlier steps and the pushout universal property. No homotopy commutativity is silently used as strict equality.

For Step 6, I read lem-coef-infinity-right-anodyne-product and lem-coef-right-anodyne-lifting-characterization. The product statement accepts any monomorphism for its other input, not only a weak equivalence; j is monic by the slice-model statement. The endpoint {1} is exactly Lambda_1^1 under the stated horn convention. Interchanging the factors identifies its pushout product with the displayed union. The lifting-characterization statement applies to arbitrary bases and gives a filler against u. Evaluation at endpoint 0 gives a strictly commuting lift. The final use of the model fibration characterization is therefore justified for every trivial slice cofibration.

I checked delivery-errors B–E against these files. There is no statement-only new node, duplicate node, new definition, Mathlib leaf, relabelled clause or enlarged hypothesis. Statements use the existing definitions and all non-elementary facts in the proof have cited statement passages. citations.json was formed from the opened JSON statements with exact substrings, not reconstructed paraphrases. All six non-elementary steps are below 1000 characters, so none reaches the 2000-character long-step threshold or hides the named fiber comparison. The proof dependency list is exactly the union of uses. An explicit dependency walk through every proposed citation found no path back to this item.

The small cases are consistent: if S is empty, then X and Y are empty and the assertion concerns the unique identity map; no choice of a vertex is demanded. Empty vertex fibers are allowed by both the slice theorem and the Kan-fibration comparison. If Y is a point the result reduces to the comparison for a Kan source, and the cylinder endpoint calculation still includes j with empty domain. In dimension one the right horn is {1}, so the correction fixes the prescribed value at time 0 using provisional data at time 1; no left/right interchange occurs. All constructions and model factorizations use the fixed small universe from the existing statements.

The item was searched with msearch.py using LeanFinder twice, LeanSearch, Loogle and grep. I read the returned all-horns Kan-model declarations in Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:34–100, and the inherited-slice declarations in ModelCategory/Over.lean:14–24 and 65–78. Neither gives the contravariant model or its right-horn comparison. Exploratory fiber searches were also logged; their all-horns hits did not supersede the existing DAG comparison node. No unrun search was added and no unavailable service was described as a negative result.

## Second reading by Q42

- Source and statement: I reread HTT Corollary 2.2.3.14 (printed pp. 86-87; PDF pages 103-104), including Corollaries 2.2.3.12-13. The arbitrary simplicial base, both right-fibration hypotheses, the slice fibration conclusion, and its converse agree hypothesis by hypothesis; no quasicategory or Kan assumption on S is present.
- Step 1: The right-horn-to-slice lifting argument uses the stated generators, slice trivial-cofibration property, and right-fibration definition; the composed structure map to S supplies the required slice square.
- Step 2: The model factorization, fibrant-object and fiberwise weak-equivalence clauses are all in `lem-coef-contravariant-slice-model`; composition of right fibrations is written by two successive horn lifts, so no closure theorem is hidden.
- Step 3: The pullback horn argument is explicit; `lem-cbc-right-fibration-space-fiber` applies because the fiber Y_s is Kan, and `lem-coef-kan-fibration-arbitrary-base-fibers` applies to the displayed map over Y_s, including empty fibers. The strict-fiber identifications with X_y and Xprime_y are degreewise correct.
- Step 4: The right-fibration presentation node states both fiberwise equivalence detection and Kan mapping complexes. It therefore supplies an inverse and a homotopy over Y; the 2-horn orientation correction is spelled out rather than hidden in “similarly”.
- Step 5: The factorization fibration gives e with ej=ia and qe=b; the endpoint equations make the two maps on the pushout agree and their composites to Y equal.
- Step 6: The inclusion of vertex 1 into Delta-1 is exactly the right horn Lambda-1-1, the pushout-product node accepts the monomorphism j, and the right-anodyne lifting characterization gives the filler whose 0-endpoint solves the original slice square. The final slice fibration criterion is the cited statement.
- New nodes: none. I checked every cited node's full statement, searched the DAG for duplicate horn, fiber, presentation, and model-structure facts, and confirmed that all auxiliary facts are either explicit in the six steps or existing nodes.
- Edge cases: empty S forces empty X and Y and gives the identity map; Y a point reduces to the Kan-fiber case; empty vertex fibers are allowed; dimension n=1 uses the right horn with vertex 1. These cases expose no missing hypothesis.
- Delivery metadata: the inherited `created` record incorrectly named `lem-coef-relative-cone-presheaf-fibers` and group `NP`; I corrected only those fields to this item and `Q42`. The statement, proof, dependencies, citations, searches, blueprint ancestry, and tool-use declaration remain unchanged. No Lean or compiler tool was run.
