Files written:

- `dag/nodes/sec-poincare-duality/lem-pod-etale-stalk-tensor-scalar.json` — statement, split proof; no new nodes.
- `citations.json` — verbatim statement excerpts for every cited node at every proof step.

Attachments: none. No `WANTED:` items.

The item was not an exact attachment. `WeilConjectures/SixFunctors/Etale/UpperLowerStar/StalkMonoidal.lean` contains a closed generic tensor-stalk declaration, but it does not state the item's scalar-extension clause or its concrete sheafification conventions. The existing lisse tensor/scalar node depends on this item, so I supplied the underlying general stalk argument rather than restating that consumer.

I read the imported item source (Stacks Sheaves Lemmas 007K and 008B, Sites Modules scalar-extension construction, and etale-cohomology Lemmas 03PT/04FM) and the statements of every cited DAG node. Step 1 uses the existing sheafification-stalk isomorphism and the geometric-stalk colimit definition. Step 2 applies the existing filtered-colimit tensor comparison to the pointed etale-neighborhood system; its statement supplies both the isomorphism and the pure-tensor formula. Step 3 uses the same comparison's naturality and checks associativity, commutativity, and unit on pure germs, which generate the colimit stalk. Step 4 repeats the colimit argument with the constant `\\Lambda'` system and the `\\mathcal F(U)` system, giving the scalar-extension map and its `\\Lambda'`-linearity. Step 5 checks successive scalar extensions on pure tensors. I verified the hypotheses: the pointed-neighborhood index is filtered, the tensor clause has commutative base ring, and scalar extension uses the stated `((\\Lambda',\\Lambda))`-bimodule structure. I also tested the edge cases of a constant sheaf and identity scalar extension conceptually; both comparisons reduce to the identity on germs.

Required Mathlib searches were run for the item with `leanfinder`, `loogle`, `grep`, and `leansearch`; LeanSearch was unavailable, and the other searches found no exact etale-site theorem. Existing DAG searches found no duplicate blueprint node or statement.

## Second reading by C1

- Item statement: checked against Stacks 007K and 008B, with 03PT/04FM for geometric-point stalks; all stated hypotheses are present.
- Step 1: checked against `lem-weil-pbc-sheafification-geometric-stalk`; its statement gives the presheaf stalk and sheafification isomorphism used here.
- Step 2: checked against `def-weil-pbc-geometric-stalks` and `lem-weil-pbc-filtered-colimit-tensor-varying-rings`; the pointed neighborhood system and pure-tensor formula are supplied.
- Step 3: checked against the naturality clause of `lem-weil-pbc-filtered-colimit-tensor-varying-rings`; coherence and uniqueness are elementary on pure germs.
- Step 4: checked against the sheafification and filtered-colimit nodes; the constant `Lambda'` system has the stated bimodule structure and gives left-linearity.
- Step 5: checked as an elementary associativity calculation on pure tensors for successive coefficient maps.
- New nodes: none; DAG search found no duplicate full etale-site statement; the lisse and topological nodes are proper specializations or have different hypotheses.
- Edge cases: zero sheaves, field coefficients, the vacuous empty scheme, and identity scalar extension all reduce correctly.
- Changes: corrected `created.item` and replaced unrelated source tag 03EL with relevant tags 03PT and 04FM; no proof statement changed.

## Review by C1


I checked the item and proof against the cited Stacks lemmas and opened each cited node to confirm that it states the stalk-as-colimit, sheafification invariance, or filtered-colimit tensor comparison used by the corresponding step. The non-elementary work is confined to Steps 1, 2, and 4 and is explicitly supplied by those nodes. Step 3 is a direct naturality and coherence calculation on pure germs, and Step 5 is the corresponding associativity calculation, so both are marked elementary. No new node was created: every dependency was searched in the DAG and the existing generic nodes are strictly more general tools. The proof uses the same tensor and coefficient-change route as the blueprint's Tensor products and Base change of coefficients paragraphs, with no additional hypotheses.
