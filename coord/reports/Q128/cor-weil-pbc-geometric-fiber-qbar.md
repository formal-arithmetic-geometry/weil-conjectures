# Q128 stage-1 direct delivery: cor-weil-pbc-geometric-fiber-qbar

## Files written

- dag/nodes/sec-proper-base-change/cor-weil-pbc-geometric-fiber-qbar.json — statement item, split into two elementary specializations of existing statements; Mathlib searches found no match. No new nodes; no Mathlib leaves.
- citations.json — one verbatim statement quotation for each of the four step/node pairs.
- report.md — this report. searches.jsonl is the unmodified command-generated search record; write_split.py is sandbox-only preparation code.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the exact blueprint tag and geometric-fiber/Qbar/base-change notions, and searched SixFunctors for the coefficient and theorem spellings. There is no project declaration giving the specified pair-category exchange together with its finite-stage representative clause. The upstream master reference is not used as evidence of a finished proof.

## WANTED

None. The current blueprint and the historical proof paragraph needed for this immediate specialization are available locally.

## Corrections and statement dispute

STATEMENT-DISPUTED: the imported phrase “in the setup of the finite-level geometric-fiber corollary” supplies only the proper/geometric-point assumptions of the finite-ring etale result. It does not on its own supply the hypotheses of the currently defined rational and Qbar categories. For an explicit domain/type check, take ell=2 and f the identity of Spec(F_2), with geometric point Spec(overline(F_2)). The finite-ring corollary's hypotheses hold, but ell is not invertible, so Dbc(T,Qbar_ell) is outside the declared domain in def-weil-pbc-qbar-category. This is a missing-domain issue, not a claimed counterexample to a correctly defined exchange.

Repaired the statement faithfully to its stated finite-extension intent by importing explicitly the scheme hypotheses of the already repaired cor-weil-pbc-geometric-fiber-finite-extension: noetherian finite-dimensional schemes, ell invertible, both vertical maps proper, and a uniform bound on the geometric-fiber dimensions of f. Fixed ell and its algebraic closure, specified the pair-category meaning of Qbar coefficients, named the geometric square and descended operations, and made the finite-stage representative precise. The displayed conclusion and representative clause are unchanged. These conditions are exactly those of the finite-extension theorem used in the source's route; they are not a replacement route. The item is not a target statement in GOAL.md.

The original proof_deps contained the finite-torsion geometric-fiber corollary without using it in any proof step. Removed this unused proof edge; finite-stage rational data are supplied by the finite-extension corollary instead. Retained historical import fields, including uses_not_cited and blueprint_uses, as instructed. No unit or chapter changes.

## Unfinished work

None for this one-level split. The existing dependent statements retain their own status and proof obligations. This split makes no comparison of the blueprint pair category with the exact upstream condensed-coefficient target.

## Blueprint searches and route

Read the chapter and sk-thm-properbasechange unit. The item is a corollary, not the unit's key statement, so the unit's realized fields are untouched. The source route is the existing Qbar proper-base-change theorem specialized to the geometric-point square, followed by its representative clause, exactly as in the master proof paragraph. The main-20261015 item has the same statement and no proof paragraph; its final sentence again points to the finite-extension geometric-fiber corollary.

Ran tools/blueprint_refs.py search for “geometric-fiber”, “geometric-fiber formula”, and “Qbar”, and searched DAG statements for the geometric-fiber words. The finite-ring and finite-extension corollaries have different coefficient categories. thm-weil-pbc-qbar is more general and is reused directly, not duplicated. No second blueprint node states the entire item separately; same_as is []. All cited statements belong to the same proper-base-change unit, so no off-unit tool declaration is needed.

## Review by Q128

I read the main-20261015 item and finite-extension corollary, the master item's complete proof paragraph, and the main Qbar theorem. I then opened the current DAG statements of thm-weil-pbc-qbar, cor-weil-pbc-geometric-fiber-finite-extension, and prop-weil-pbc-scalar-extension, rather than relying on their titles or their proofs. For the hypotheses and notions I also read the current Qbar category, rational finite-extension theorem, descended functors, cartesian square, proper morphism, geometric point, fiber product and dimension statements. No new node was needed, so there is no new-node literature claim to audit.

Step 1 takes the isomorphism for the specified descended exchange from thm-weil-pbc-qbar. Substituting Y'=P, X'=X_ybar, g=ybar, g'=i_ybar, f'=a_ybar literally produces the displayed source and target. The chosen fiber product provides the cartesian identification. Properness of f is a hypothesis, and the theorem explicitly permits arbitrary g. The repaired statement supplies the scheme and finite-coefficient domains, including the stronger assumptions of the finite-extension theorem underlying it. There is no additional properness deduction hidden in this step: properness of a_ybar is explicitly among the inherited hypotheses. I marked this step elementary because its only argument is substitution into the cited theorem, not a new base-change proof.

Step 2 uses the actual representative sentence of thm-weil-pbc-qbar: it gives this component, not merely some isomorphism, as the M-coefficient exchange on T_{M/E}K_E with its comparison identifications. The exact-functor statement of prop-weil-pbc-scalar-extension supplies membership of that object in Dbc(X,M). The finite-extension geometric-fiber corollary states the exchange for precisely the same square and raw rational operations. Its hypotheses do not change when the coefficient field is replaced by M. Thus the maps agree by their specified construction; no appeal to uniqueness of arbitrary isomorphisms or a new comparison lemma is required. This is another elementary instantiation of the cited statements. citations.json quotes the statements verbatim and records every proof citation.

Against delivery-errors B, there are no statement-only child nodes, new-node fields, invented Stacks citations, or claimed Mathlib matches to check. All searches were run using msearch.py; the results were read and are recorded with the exact tool/query text. LeanSearch returned geometric stability facts, the first LeanFinder returned scheme pullbacks and module-functor comparisons, and the second returned ordinary topological stalk maps; none supplies this derived Qbar theorem. Loogle returned no hits. Grep found general base-change stability and the coefficient-field abbreviation, not the required exchange.

Against C and D, every nontrivial assertion is the statement of an existing cited node, proof_deps is exactly the union of uses, no node's proof is used as an interface, and no new clause-restatement node or cycle is introduced. Against E, the missing coefficient-domain hypotheses were repaired explicitly. The zero complex and identity proper morphism are allowed; choosing M=E is consistent with identity scalar extension. An empty geometric fiber is not excluded: all fiber-dimension bounds are upper bounds on nonempty fibers, and neither specialization assumes a fiber has a point. Geometric fields of characteristic ell are excluded explicitly by invertibility, as required. The argument changes neither the ringed exchange nor its comparison choices when renaming the arrows. Both proof steps are below 2000 characters and contain no independent hidden lemma. No prohibited SGA source or compiler/build tool was used.
