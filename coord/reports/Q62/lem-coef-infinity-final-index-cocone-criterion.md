# Q62 worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-final-index-cocone-criterion.json: the item, split into five proof steps. No new nodes and no Mathlib leaves.
- citations.json: seven step/node pairs, each quoting the cited statement verbatim. The full statements are retained so that all clauses used by a step are visible together.
- searches.jsonl: six fresh search-command records concerning the full mapping-space evaluation assertion. Seven existing search entries in the item were preserved.
- report.md: this report. write_split.py is a sandbox-only preparation script.

## Attachments

None. Searches for the exact blueprint tag and for quasicategory, final/terminal indexing objects, coherent cocones and colimits in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no project declaration stating the item. The ordinary-category results in Mathlib are not attachments. No Lean was written, no compiler or Lake tool was run, and the upstream master declarations were not treated as proofs.

## Sources wanted

WANTED: an archived copy of Kerodon 02XV (Corollary 7.2.2.5), 03LQ (Example 7.2.1.4), 02XU and 02XY, for the item. I read those online. These are Kerodon identifiers, not Stacks tags: Stacks does not state this theorem for arbitrary quasicategories. Also read online the supporting composition subsection 01PF and coherent Hom-functor naturality 046J/03PD. No source was downloaded or written to literature/.

The proof_origin is agent: the proof is written from the existing DAG interfaces and checked against these online sources, which are not archived under literature/. The inherited blueprint ancestor and its current main-20261015 statement and proof were read. The item is a generic tool in the inherited adjunction infrastructure, not a new geometric route or a key statement of the unit.

## What was wrong or needed clarification

The starting item was statement-only, not a split. Its statement is correct and was kept verbatim. In particular, its second clause refers to initiality in the coherent comma cocone category; the mapping-space definition used by final-index-colimit alone does not supply that translation. Step 3 now cites the precise dual comma mapping-space criterion of lem-cbc-enhanced-functor-cone-calculus. This is declared as a generic off-unit tool in split_report.tool_uses, not written to the maintainer-owned tool_uses field.

The existing source note correctly observes a rendering typo in Kerodon 02XV: the final-object/colimit clause displays a left cone and an inconsistent indexing-category letter. Its right-cone restriction, the dual limit clause and 03LQ/02XY identify the intended theorem. The item already spells out the correct coherent cocone assertion, so no statement dispute or hypothesis change is needed.

At startup the shared snapshot did not yet expose this newly created item. It appeared during synchronization; I then copied that current shared item and retained its exact statement, source, creation record, blueprint ancestry and seven previous search entries. There was no earlier Q62 split, report or search log to overwrite. Some initial discovery commands inadvertently ranged beyond the named directories and included a read-only git probe outside the shared repository; these were unnecessary and I stopped using them. No shared project, live source, launcher, or other worker file was modified. All files prepared for this delivery are in this item's Q62 sandbox.

## Not duplicates

No new node was created. Whole-DAG searches by 02XV/03LQ and final-index/cocone terminology, and whole-blueprint searches by final object, terminal object and cocone found no blueprint statement equivalent to the item; blueprint.same_as remains []. Existing final-index-colimit supplies the identity-leg colimit, and existing mapping-space composition, Hom-functor naturality and coherent comma calculus supply all remaining ingredients. The direct two-object inverse argument is a step, not a new Yoneda lemma or a restatement of an item clause.

## Review by Q62

I read the worker brief, stage-1 rules, delivery-errors sections B through E in full, GOAL.md and dag-sync.md. I read the chapter and unit records, the three-level restrictions in SETUP.md, and the current main-20261015 statement and proof of prop-coef-integral-exceptional-adjoint. I kept the chapter, unit and inherited ancestry. No target statement, coefficient category, base-change map, geometric hypothesis or unit realization field changes, and no SGA source is used.

I read the statement of every cited node in full: lem-coef-infinity-final-index-colimit, lem-cbc-enhanced-functor-cone-calculus, lem-coef-infinity-hom-bifunctor-functoriality and lem-coef-infinity-mapping-composition. I also read def-cbc-enhanced-diagrams-cones to check the right-pinched mapping-space, equivalence-edge and coherent comma-category conventions. Each proof citation is a statement use, never an appeal to a fact hidden in a cited proof.

Step 1 applies the existing final-index-colimit node with exactly J, t and d. Its contractibility hypothesis is the item's hypothesis, and its statement explicitly gives both the identity leg and the universal mapping-space maps. It does not require cocompleteness. The cone-calculus node separately says Fun(J,C) is a quasicategory and its mapping spaces are Kan. J is small in the chosen containing universe, so that hypothesis is satisfied; the space universe can contain all mapping simplicial sets without imposing any new mathematical restriction.

Step 2 uses the Hom-bifunctor node, whose statement explicitly identifies induced maps with the actual right-pinched simplicial maps and says they preserve composition and identity classes, with higher naturality. Applied to evaluation and the constant functor, this gives r_w c_w homotopic to the identity on the whole space. Evaluation composed with the constant functor is strictly the identity in every simplicial degree. The elementary two-out-of-three conclusion is written out on components and based homotopy groups, including the basepoint identifications from the homotopy. Thus this proves the actual evaluation map is a weak equivalence, rather than merely constructing some equivalence between its source and target.

Step 3 uses the dual assertion of the cone-calculus statement: it identifies initiality in the coherent cocone category with the specified cocone's universal mapping-space maps q_w being equivalences for every w. This is exactly the missing translation between the two colimit conventions. Hom-functor naturality again identifies r_w q_w with precomposition by the actual component mu_t. All targets w are quantified, and the previous step applies to each of them. Consequently the reduction is an iff about the given cocone, without choosing a replacement cocone or using a limit-existence theorem.

Step 4 uses the mapping-composition statement's homotopy associativity and unitality and its dependence only on component classes. If the final leg has inverse g, precomposition by g has the two required inverse homotopies on entire mapping spaces. Its source and target directions are checked: precomposition by f maps Map(l,w) to Map(a,w), and precomposition by g goes back. The weak-equivalence conclusion follows from inverse induced homotopy-group maps, then Step 3 gives initiality of the original cocone.

Step 5 uses only the induced bijections on components and the ordinary category hC and inverse-edge criterion stated in mapping-composition. With w=a, surjectivity produces [g][f]=id_a. With w=l, injectivity gives [f][g]=id_l after composing both candidates with [f]. Every component has an edge representative by the cited statement. The cited equivalence between invertible component classes and actual inverse-triangle witnesses then gives the item's precise definition of equivalence edge. No general Yoneda theorem, representability assertion, or hidden additional lemma is used.

I checked small cases. For J=Delta^0, evaluation is the identity and the criterion says a single edge is colimiting exactly when invertible. For J=Delta^1 with terminal endpoint 1, the other diagram edge is unrestricted; the proof tests the final leg only. Empty J has no t and cannot satisfy the hypotheses. Empty C admits no diagram from a J containing t, so the assertion is vacuous. Empty target mapping spaces cause no nonemptiness assumption in Steps 1-4; in Step 5 the required nonempty source component is forced by surjectivity onto the identity at a. The proof needs no global colimits in C.

I retained all seven previous search records after reading their results and the relevant Mathlib sources. The new search question asks specifically about full evaluation on coherent cocone spaces, rather than merely colimit existence; I ran six fresh commands via msearch.py, with two semantic phrasings, Loogle, LeanSearch and source grep. All services returned successfully. I read Final.lean:283-295 and IsTerminal.lean:383-404: they require ordinary categories. I read Types/Colimits.lean:39-49: its cocone equivalence is for ordinary Type-valued diagrams. I read Coskeletal.lean:68-88: its lift requires StrictSegal and constructs simplices for a coskeleton comparison. I read HomotopyCat.lean:560-569: its terminal theorem concerns the entire terminal simplicial set. None is the item's arbitrary-quasicategory mapping-space theorem. The inherited failed Loogle identifier pattern remains honestly recorded as a rejected query, without an absence conclusion.

I checked B-E point by point: there are no new unsplit nodes, no duplicate child statements, no relabeling of clauses as children, and no uncited non-elementary result. The two-out-of-three and two-test-object algebra are short explicit steps from the cited interfaces and definitions. Every step is below 1100 characters, so no step crosses the 2000-character review threshold. proof_deps is exactly the union of uses. The four cited lemma closures do not contain this item, so these citations introduce no cycle. citations.json quotes each statement verbatim, including the dual cocone clause where it is used. The only off-unit statement use is declared with its exact purpose. The server check_dag and review_split checks passed on resumption. The first full dry run rejected the phrase “the item's definition” in Step 5 as not self-contained; I replaced it with the explicit definition by an inverse edge and two inverse-triangle simplices, restated the objects a and f there, and clarified the coherent cocone definition in Step 3. These are expository repairs; the statement, citations and argument are unchanged. A final full dry run and push follow these corrections.

## Unfinished work

No mathematical part of the one-level split remains. There are zero new nodes and zero Mathlib leaves. The supporting existing lemmas retain their own states; this stage-1 delivery makes no claim that their Lean proofs are finished.
