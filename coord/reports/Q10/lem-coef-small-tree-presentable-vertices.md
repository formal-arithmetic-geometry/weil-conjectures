# Worker report: lem-coef-small-tree-presentable-vertices

Files written:

- `dag/nodes/sec-six-functors/lem-coef-small-tree-presentable-vertices.json` — completed the imported statement node with a three-step proof; no new nodes were required.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

Attachments:

- None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream reference source for the item id, cellular-tree terms, and presentable-vertex terms; no project declaration states this item without `sorry`.

WANTED: HTT, Definition A.1.5.1, Notation A.1.5.2, and the compact endpoint observation after Lemma A.1.5.11 / Proposition A.1.5.12 (printed pp. 799-800 and 808-809), because the cited PDF is not archived under `literature/`.

What was wrong in the imported node:

- The statement was unsplit and had no proof. I retained every hypothesis and conclusion and filled the blueprint location. The proof uses the existing Mathlib leaf for colimits of fewer-than-`tau` presentable objects; no clause was moved into a new node.

What I could not finish:

- Nothing in the stage-1 split remains unfinished.

## Review by Q10

I read the item node, `def-coef-good-cellular-tree`, `def-weil-pbc-category-colimit`, and `lem-coef-ordinary-small-colimit-presentable`, together with the unit and blueprint ancestry. On resumption I read the cited HTT PDF online: Definition A.1.5.1 and Notation A.1.5.2 on printed pp. 799–800, Lemma A.1.5.11 and the use following it in Proposition A.1.5.12 on printed pp. 806–809. The PDF is not archived under literature/, so the retained WANTED line concerns the missing local copy. The proof remains marked agent-written: the needed induction is supplied here rather than claimed as the verbatim statement of an HTT lemma.

Step 1 uses the cellular-tree definition for the diagram under the root and the colimit definition for the universal-property calculation identifying an undercategory restricted colimit with the ordinary colimit of the diagram obtained by adjoining the root. It explicitly handles the empty restriction and counts the augmented diagram's morphisms using `|T|<tau`.

Step 2 uses the cellular-tree definition for the predecessor colimit and specified pushout square, and uses the Mathlib statement that a colimit of `tau`-presentable objects indexed by fewer than `tau` morphisms is `tau`-presentable. The well-founded induction supplies presentability of every strict predecessor; the root and both cell endpoints are hypotheses. I verified that the empty predecessor case is covered by the augmented root diagram and that the finite span has fewer than `tau` morphisms.

Step 3 applies the same cited Mathlib statement to the augmented restricted diagram for an arbitrary downward-closed subset. It therefore covers all predecessor restrictions and the total object, while Step 1 gives the empty restriction as `M`. The hypotheses used are exactly the item's root, endpoint, cardinality, and colimit assumptions; no presentability of the original ambient root beyond the stated `M` is introduced.

I tested the edge cases of an empty tree, a one-cell tree, a chain, and a disconnected set of cells. No new node was created because the only non-elementary ingredient is already the Mathlib leaf `lem-coef-ordinary-small-colimit-presentable`, and the undercategory-to-augmented-diagram calculation is a short universal-property step from the cited definition.


Resumption review (2026-10-17): I compared the saved item with the current repository. Only the split-owned proof, blueprint location, status and report fields differ; its statement, hypotheses and original Mathlib search history are unchanged. There is no sandbox searches.jsonl to reread: the searches were inherited from this existing item, not invented in this delivery. I retained all recorded queries and unavailable-service verdicts. The repeated declaration search found no exact project theorem; the whole-blueprint cellular-tree search returned no match. Reading Mathlib/CategoryTheory/Presentable/Limits.lean:185–195 confirms the cited theorem requires presentability of all diagram values and the bound on morphisms, both verified in Steps 2 and 3. None of the nearby descent or approximation nodes states this fixed-root induction.

The first required resumed dry run exited successfully at 3b5183e3e7. I then corrected the direction of the root maps in Step 1, explicitly cited the cellular-tree statement there, and wrote out both directions of the cocone calculation with the root map fixed. I made the morphism bound explicit using the ordered-pair bound for a poset, and retained the empty-root case. The cellular-tree statement supplies exactly the canonical predecessor map and specified pushout used in Step 2; no assertion is borrowed from a cited node's proof. The only non-elementary input remains the existing presentability Mathlib leaf. No new unsplit statement, duplicate, clause-restatement node, source-route change, extra hypothesis or cycle was introduced. Every step is below 2000 characters, and the direct universal-property calculation is a routine argument rather than a hidden lemma. All seven citation entries are verbatim in the current node statements and cover every step/node pair.

Online source checked: [Lurie, Higher Topos Theory](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), the definition, notation and compact-cell argument at the places above. No SGA source was used.
