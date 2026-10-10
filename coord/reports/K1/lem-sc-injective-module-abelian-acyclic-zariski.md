1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-injective-module-abelian-acyclic-zariski.json`: split statement, no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-injective-module-cech-acyclic.json`: statement-only node, Mathlib no match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-cech-vanishing-criterion.json`: statement-only node, Mathlib no match.
- `citations.json`: verbatim step citations.

2. Attachments: none. No sorry-free slopmaster2 declaration for the item or either new statement was found by searching the source tree and comparator names.

3. WANTED: none; the cited Stacks source is represented in the local citation metadata and the existing DAG source records.

4. What was checked and changed: the imported item is exactly the second-paragraph conclusion of Stacks Tag 03FD, with the arbitrary ringed-site hypotheses retained. The nearest blueprint ancestor is `lem-sc-ga-cohomology`; the item blueprint place and both new-node `from.place` fields identify the two clauses of that paragraph. The first new node isolates the non-elementary Tag 03FC fact that an injective module sheaf has vanishing Cech cohomology after forgetting to abelian sheaves. The second isolates Tag 03F9, the Cech-to-derived vanishing criterion. I searched the full DAG and blueprint before creating both nodes; existing etale and Zariski Cech nodes are specialized statements and do not state these arbitrary-site facts, so citing them would violate C4. Each proof step cites exactly the statement it uses, and `proof_deps` is the union of those citations. Small cases checked: on a one-object site the Cech complex is concentrated in degree zero, and for the zero module sheaf all Cech and derived groups vanish. The Mathlib searches recorded for each new node found only generic Cech or injective-resolution ingredients, not the needed theorem.

## Review by K1

I read the item source as Stacks `sites-cohomology.tex`, Tag 03FD, second paragraph, and checked the statement against its arbitrary ringed-site formulation. I also read the existing DAG nodes for the related etale proof (`lem-weil-pbc-injective-module-abelian-acyclic`), the Zariski specialized Cech lemma, and the general abelian Cech acyclicity node. Those existing nodes either specialize the site or assume abelian injectivity, so neither states the fact used here. Step 1 uses only the new 03FC statement, whose sentence explicitly gives the underlying-abelian Cech complex and its positive-degree vanishing. Step 2 uses only the new 03F9 statement, whose hypothesis and conclusion exactly match the Cech vanishing established in Step 1. Both steps are non-elementary and are marked accordingly. I verified that all hypotheses (ringed site, module injectivity, arbitrary covering, and positive degrees) are present where used, and that the statements remain true for the zero sheaf and the one-object site. I corrected the initially empty proof by making the two hidden Stacks lemmas explicit and adding their blueprint references, Mathlib searches, and verbatim citations.

5. What could not be finished: no Lean code is written at stage 1, and the two supporting nodes remain intentionally unsplit statement-only queue nodes.
