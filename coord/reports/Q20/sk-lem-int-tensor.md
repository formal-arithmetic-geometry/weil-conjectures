## Files written

- `dag/nodes/sec-six-functors-basics/sk-lem-int-tensor.json`: split the item into three proof steps; no new nodes.
- `dag/units/sk-lem-int-tensor.json`: recorded the item as the realized statement and the three existing route lemmas as realized steps.
- `citations.json`: verbatim statement quotes for every cited step.

## Attachments

No Lean declaration is attached: the source search found no declaration tagged `sk-lem-int-tensor`, and no declaration states this item exactly without `sorry`.

## WANTED

None.

## What was wrong in the imported node

The imported proof had four paragraphs and cited several restricted-functor definitions and a rational two-colimit theorem that are outside the item statement and were not needed to prove it. The unit route already has the three existing lemmas `det-lem-int-tensor-shriek`, `det-lem-int-tensor-pullback`, and `det-lem-int-tensor-product`; the split now uses those directly. The statement itself agrees with the main-20261015 blueprint and was left unchanged.

## What could not be finished

Nothing remains for this stage-1 split. The cited child nodes are existing DAG nodes; no new node or Mathlib leaf was created.

## Review by Q20

I read the item source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/_section.md`, the chapter record, and the unit record. I also read the complete source files for `det-lem-int-tensor-shriek`, `det-lem-int-tensor-pullback`, and `det-lem-int-tensor-product`, together with their DAG statements. Step 1 cites `det-lem-int-tensor-shriek`; its statement explicitly gives preservation of `Dbc` by open extension and closed direct image and the finite extension closure by locally closed stratum models, so it supplies every assertion used in that step. Step 2 cites `det-lem-int-tensor-pullback`; its two numbered conclusions explicitly give inverse-image preservation and the completed Stacks inverse-image comparison. Step 3 cites `det-lem-int-tensor-product`; its first paragraph states exactly uncompleted tensor closure for two integral bounded constructible objects, and its moreover clause states the dualizability and derived-limit preservation used by the local-model dévissage. I checked the hypotheses match the item: Noetherian/standing schemes and the same `\\mathcal O_E` coefficient category are retained. I removed the imported restricted-functor paragraph and its unrelated dependencies, filled the blueprint search result as `same_as: []`, and recorded the three route steps and their exact statement quotes.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against the blueprint item and `det-lem-int-tensor-shriek`: the cited statement supplies both preservation clauses and the finite stratum-extension dévissage under the standing Noetherian hypotheses; verdict correct.
- Step 2 checked against the blueprint item and both numbered clauses of `det-lem-int-tensor-pullback`: inverse-image preservation and the completed Stacks comparison are stated with the required morphism and coefficient hypotheses; verdict correct.
- Step 3 checked against the blueprint item and `det-lem-int-tensor-product`: the uncompleted tensor closure conclusion and the local-model dualizability/limit-preservation clause justify the step; verdict correct.
- No new nodes: there are no new statements to audit for B1–B7; grep of `dag/nodes` found the three cited route lemmas and no duplicate node was introduced.
- Statement edge cases checked from the definitions: zero complexes and the empty scheme are vacuous, a field gives the stated finite-free local models, and the assertions remain meaningful for the identity morphism and zero tensor factors; verdict faithful to the source.
- Blueprint check: the item is itself an imported blueprint node, so its required `blueprint.from` is null; `same_as` records the completed whole-blueprint search as empty.
- Confirmed the imported item's blueprint ancestry metadata remains null; no mathematical statement or proof step was changed.

## Second reading by Q20

- Item statement: checked against the blueprint node `sk-lem-int-tensor` in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/_section.md`, including the standing-scheme, morphism, coefficient, completion, and uncompleted-tensor hypotheses; verdict faithful. The Stacks sources named by the imported external references were read in `proetale.tex`: Tag 09AA (`lemma-closed-immersion`), Tag 09BM (`lemma-closed-immersion-complement-retrocompact-exact`), and Tag 09BP (`lemma-j-shriek-limits`); their hypotheses and conclusions agree with the operations used by the cited route lemmas.
- Step 1: checked against the statement of `det-lem-int-tensor-shriek`; its two numbered conclusions explicitly give preservation by open extension/closed direct image and finite stratum-model dévissage under a standing Noetherian scheme. Verdict correct; no uncited non-elementary fact is used.
- Step 2: checked against the two numbered conclusions of `det-lem-int-tensor-pullback`; they state `Dbc` preservation and the completed inverse-image comparison after restriction of scalars for the same morphism and coefficient ring. Verdict correct.
- Step 3: checked against both paragraphs of `det-lem-int-tensor-product`; the first is the exact uncompleted tensor-closure conclusion, and the moreover clause explicitly supplies dualizability, product/derived-limit preservation, and preservation of derived completeness for local models. Verdict correct after replacing the vague reference to a local-model argument with these stated properties.
- Existing-node audit: searched `dag/nodes` for all three cited tags and identifiers; each cited node is unique and already present, so no duplicate or new node is needed. No Mathlib leaf or new definition node was introduced.
- Edge cases: the zero complex and zero tensor factor remain in `Dbc`; over a field the local model is a bounded finite-free complex; on the empty scheme the claims are vacuous; identity morphisms preserve all stated structures. Verdict faithful.
- Changes made: tightened proof step 3 to name the exact clauses supplied by `det-lem-int-tensor-product`; appended this independent second-reading record. No statement, dependency, or citation quote was otherwise changed.
