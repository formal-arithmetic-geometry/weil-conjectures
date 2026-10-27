# Stage-1 report: lem-sfb-almost-filtered-components

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-almost-filtered-components.json: statement; split into six elementary proof steps; Mathlib verdict no match.
- citations.json: verbatim statement excerpts for the two node citations in steps 3 and 6.
- searches.jsonl: actual searches made by the required msearch.py command; inherited item searches also retained in the node.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, almost-filtered, filtered components, split-into-directed, and Ore. The filtered 2-colimit characterization hit concerns a different statement, not the present decomposition criterion.

## Wanted sources

None. The source is available locally: literature/stacks-project/categories.tex, Tag 002X, label lemma-split-into-directed, statement and proof at lines 2451-2475. Tag checked against literature/stacks-project/tags/tags.

## Corrections and inherited metadata

The imported statement is correct and unchanged. The proof was empty. The source says that the rest follows from definitions; the split now writes out all of it, including transitivity and membership of the targets in the appropriate class. No hypothesis or conclusion was changed.

Read the chapter record, the assigned unit record and the latest blueprint direct-images proof (3). This generic categorical prerequisite remains on the inherited route through Tag 002Y and the site left-adjoint argument. No unit realization fields need changing: the item is not its unit's key statement.

The inherited blueprint.from.node is null. The required ancestor command reports None; the detailed from.place and via chain already explain the connection to det-thm-sf-ctf-stability-direct-images, proof (3). These inherited fields were preserved. The whole imported blueprint searches for 002X, filtered components and disjoint filtered returned no matching blueprint node; same_as remains [].

## Not duplicates

No new nodes. Whole-DAG searches by tag, label and filtered-component keywords found this item, its parent lem-sfb-almost-filtered-set-colimits, and the site-left-adjoint node. The parent proves preservation of set fibre products and equalizers, not this decomposition. The site-left-adjoint node concerns a functor on sheaves. Neither supplies a replacement attachment.

## Review by Q23

I read the statement and complete proof of Stacks Tag 002X (lemma-split-into-directed). It uses exactly hypotheses (a) and (b) of the item. No other theorem is cited by that proof. I also read both dependency statements in full: def-weil-size-convention specifies the containing universe; def-weil-pbc-category-colimit explicitly defines filteredness by nonemptiness, common targets and coequalization of parallel pairs. citations.json quotes those statements verbatim, rather than treating either definition as an existence theorem.

Step 1 defines the relation explicitly, and identities and exchange of witnesses prove reflexivity and symmetry. It uses no node theorem. Step 2 proves transitivity: the two arrows with source y are precisely a span to which (a) applies; composing the outer arrows gives the required witness. No pre-existing common-target property is assumed. Step 3 takes the elementary quotient set of a small object set. Equivalence classes form a partition and are nonempty by definition. Its citation of def-weil-size-convention fixes only the universe, and ordinary set quotients and subsets stay in that universe. It does not infer a new size or existence theorem from that citation.

Step 4 uses a morphism and the identity of its target to put its endpoints in the same class. Step 5 chooses a witness for the defining relation, then applies step 4 to prove that its apex belongs to the class; fullness supplies the arrows in the subcategory. Step 6 applies (b) to a genuine parallel pair, uses step 4 to retain the coequalizing target in the class, and invokes only the three-clause definition in def-weil-pbc-category-colimit. Thus every cited node says exactly what the step takes from it. Every other argument is a two- or three-line use of the hypotheses or elementary set/category definitions. There is no uncited non-elementary theorem, moved clause, hidden comparison, or long step; the longest step has 498 characters. No helper node would survive the elementary-node rule.

I tested the empty category (J is empty), a one-object identity category (one filtered class), and a discrete two-object category (two singleton classes, not one filtered category). A walking span satisfies (a) only when a common continuation exists, which is exactly what transitivity uses. A one-object nontrivial group satisfies (a) but fails (b): invertibility would force a=b. Thus the argument does not incorrectly assert filteredness from (a) alone. In a general one-object category satisfying both assumptions the sole class is filtered, as the three conditions require.

For delivery-errors B, no new statement-only node, undefined specialized notion, unverified leaf or duplicate was introduced; source tag and label were checked. For C, both cited statements were opened, quotes checked as substrings, and proof_deps equals the union of uses. There is no off-unit statement theorem used as a tool. For D, the actual equivalence-relation and full-subcategory arguments remain in the item; nothing was moved to a restatement. For E, all arrows' sources/targets and class memberships were checked explicitly and no missing hypothesis or source error was found.

Mathlib searches ran through the required command using LeanFinder (two phrasings), Loogle, LeanSearch and grep. I read Filtered/Basic.lean:76-98 and ConnectedComponents.lean:135-180. IsFilteredOrEmpty requires common targets for every pair, and IsFiltered.span/isConnected run in the opposite direction. Decomposed/decomposedEquiv provide connected components but not their filteredness under the two hypotheses. IndParallelPairPresentation.hI and instIsFilteredI refer to a specific presentation category. Hence none is an exact match or a one-line specialization of the item. All new log entries are preserved without claiming unavailable searches succeeded.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled, no agents were started, and no repository or launcher files were changed.
