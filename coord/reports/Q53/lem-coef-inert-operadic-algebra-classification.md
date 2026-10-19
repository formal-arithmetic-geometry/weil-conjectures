# Q53: lem-coef-inert-operadic-algebra-classification

## Files written

- dag/nodes/sec-six-functors/lem-coef-inert-operadic-algebra-classification.json: existing statement, now split in four steps; no Mathlib match.
- citations.json: verbatim statement quotations for every step/node pair.
- searches.jsonl: actual Mathlib search records, retained verbatim; prepare.py is sandbox-only preparation code.

No new DAG nodes, no Mathlib leaves, no unit/chapter edits. The statement, its hypotheses, source, and maintainer-owned fields are unchanged.

## Attachments

None. Searched WeilConjectures/ in the slopmaster2 source for the exact item id and for inert operads, trivial operads and color diagrams. No declaration matched. The master checkout was not treated as proof evidence.

## WANTED

WANTED: Gepner–Haugseng, Enriched infinity-categories via nonsymmetric infinity-operads, arXiv:1312.3178v4, Definition 3.4.1, Remark 3.4.3, Lemma 3.4.4 and Proposition 3.4.5, for lem-coef-inert-operadic-algebra-classification. Read online at https://arxiv.org/html/1312.3178v4, section 3.4; the archive under literature/ is missing. No document was downloaded. The proof is marked agent because its only mathematical black box is the existing DAG reconstruction theorem and the remainder is the direct restriction calculation. No Stacks tag states this infinity-operadic assertion.

## Issues found and reuse

The existing reviewed lem-coef-inert-operad-color-reconstruction already states the classification needed here, including generalized operad axioms, the identity zero-fiber map, all higher simplices, and absence of colimit/presentability assumptions. Its reviewer explicitly noticed the overlap with this item. I reused it rather than inventing another reconstruction or right-Kan lemma. The present item records the pre/postcomposition identities explicitly. Merging duplicate IDs belongs to the maintainer, so no merged_into field was changed.

The ordinary enriched-category and monoid-object search hits are not infinity-operadic classification results. Read Enriched/Basic.lean:58-69 and Monoidal/Internal/FunctorCategory.lean:43-87; their categories are ordinary Lean categories. The two semantic phrasings returned simplicial objects, nerves and ordinary equivalences, not a match. All five new searches were made through the required msearch.py command, and their actual results are recorded alongside the original inherited searches.

## Not duplicates

No new nodes. lem-coef-inert-operadic-algebra-classification vs lem-coef-inert-operad-color-reconstruction: the existing reviewed reconstruction statement contains the core assertion, and step 2 cites it. The extra functoriality in the item is proved by restriction identities. These are intentionally reused statements, not a newly named version of a clause. The DAG/blueprint searches found no imported blueprint counterpart (searched trivial operad, inert, and inert operad algebras color diagrams). The existing node is in this same unit.

## Review by Q53

I read the item, sec-six-functors chapter record, sk-prop-sf-biduality-general unit record, the three-level rules, the current main-20261015 ancestor proof and delivery-errors B–E. The chapter record happens to name a newer unavailable snapshot; I used the brief's current main-20261015 text and retained the inherited ancestry. This node supplies an operadic foundation under paragraph 2's coefficient adjunction, and changes no geometric or coefficient route. There is no base-change morphism in its statement.

For the source I read GH section 3.4 online, especially the opening classification paragraph, Definition 3.4.1's pullback, Remark 3.4.3's Segal description, and Proposition 3.4.5's natural equivalence on algebra infinity categories. The target V^tensor is a monoidal infinity category, hence a nonsymmetric infinity operad with terminal zero-fiber; the source M is allowed to be generalized. Proposition 3.4.5 therefore has the intended color-functor target. No cocompleteness, accessibility or presentability of V is required. I also read the full statement and final naturality step of the existing reviewed reconstruction node. No new node needs a separate source.

Step 1 uses def-coef-monoidal-infinity-category for the consecutive-subinterval meaning of inert maps, lem-coef-operadic-algebra-presentability only for its generalized operad definition, and lem-coef-inert-operad-color-reconstruction for the hypotheses of the theorem being applied. I compared the definitions: both have an inner fibration, inert cocartesian lifts, the same fiber-product Segal rule including arity zero, and the full incidence mapping-space axiom with vertices AND edges. The item explicitly assumes smallness and Kan zero-fiber. The elementary step only matches these inputs; it does not purport to prove reconstruction.

Step 2 takes exactly the conclusions of the reconstruction node's statement: small generalized trivial operad, inert-preserving tau, identity on zero-fiber, equivalence by restriction, and all higher simplices without presentability. The base pullbacks are identical: int and inert denote the same wide base subcategory. I checked the entire dependency closure (686 IDs in this snapshot) and it does not reach this item. Citing the reviewed existing theorem thus causes no cycle. This is reuse of a previously split node, not a new node carrying the item wholesale.

Step 3 uses the monoidal definition for lax functors: they are functors over the same base preserving inert edges, exactly what composition of algebra functors requires. Both naturality squares are proved directly, by evaluating the identical composite on K times the color fiber. This works for every parameter K and restricts along its faces and degeneracies, so includes transformations and higher homotopies; it never asserts that arbitrarily chosen quasi-inverses strictly commute. The actual E maps are restriction maps. This elementary calculation supplies the item's explicit lax-monoidal compatibility without silently strengthening the statement of a cited theorem.

Step 4 uses no theorem: restriction along tau followed by inclusion of the color fiber is inclusion of that fiber in M. The same identity applies to parameterized diagrams. This proves the color evaluation clause without appealing to an uncited non-elementary fact.

I checked arity zero (the identity zero-fiber and empty tuple in V^tensor), empty M (both diagram categories terminal), M = Delta^op (trivial-operad algebras are single objects of V), disconnected Kan zero-fibers (no replacement by a point was made), and u or F equal to the identity (naturality reduces to identity). For composite u and F the same restriction identities compose, so no missing coherence is hidden. The proof uses only two definition-bearing nodes and the existing reconstruction theorem, whose quoted statement really provides every non-elementary assertion used. All citation quotes were checked as substrings of the current statements. No new non-elementary claims are hidden in long steps: every step is below 2000 characters. No SGA source is used, and no statement dispute or hypothesis change was necessary.

## Unfinished

Nothing in the stage-1 split remains unfinished. Its cited existing reconstruction theorem has its own already reviewed split. Delivery validation follows below.
