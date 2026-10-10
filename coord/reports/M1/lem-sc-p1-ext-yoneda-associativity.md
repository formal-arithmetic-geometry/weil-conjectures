1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-yoneda-associativity.json`: statement, split proof, no Mathlib leaf.
- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-yoneda-splicing-associative.json`: statement-only dependency, Mathlib generalization only.
- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-pushout-postcompose.json`: statement-only dependency, no Mathlib match.

2. Attachments: none.

3. WANTED: the local checkout does not contain the Stacks source files; the split cites `literature/stacks-project/derived.tex` Tag 06XP and `literature/stacks-project/homology.tex` Tag 010I as required by the imported node.

4. The imported item had no proof. I split its two non-elementary ingredients rather than restating the item: associativity of Yoneda splicing and identification of a pushout extension with postcomposition by the coefficient morphism. The final step is the degree-zero/degree-one specialization of associativity. The existing boundary-composition node was searched and does not state the pushout class formula, so it was not cited.

## Review by M1

I read the item, its `thm-sc-p1-duality` blueprint ancestor, and the neighboring `lem-sc-p1-ext-yoneda-functoriality`, `lem-sc-p1-boundary-extension-composition`, and `def-sc-ext-sheaf` nodes. I searched the whole DAG and blueprint for Yoneda associativity and Ext pushout statements before creating the two new nodes; neither statement already existed. I also searched the slopmaster2 source for the item tag and keywords and found no exact declaration.

Step 1 cites the new splicing node, whose statement explicitly supplies associativity for three composable Ext classes. Step 2 cites the pushout node, whose statement explicitly supplies the pushed-out short exact sequence and its class `\\varphi[1]\\circ\\delta`. Step 3 uses those same two statements and only substitutes `e=s`, `f=\\delta`, and `g=\\varphi[1]`; that algebraic specialization is elementary. Every citation quote in `citations.json` is copied verbatim from the cited node statement. The hypotheses in both new statements introduce the ringed space, modules, exact sequence, Ext classes, and coefficient morphism they use.

For small cases, I checked the consequence when `s` is the zero morphism (both sides are the zero Ext class) and when `\\varphi` is the identity (the pushout is the original extension). The imported `def-sc-ext-sheaf` is flagged elsewhere as a definition issue: it says right derived functors of contravariant `Hom(-,G)`, while the standard sheaf Ext construction derives `Hom(F,-)` in the second variable. I left the target statement unchanged and recorded this limitation rather than silently changing it.

5. What I could not finish: no Lean proof was written, as required for stage 1; the two new nodes are intentionally statement-only and enter the unsplit queue.
