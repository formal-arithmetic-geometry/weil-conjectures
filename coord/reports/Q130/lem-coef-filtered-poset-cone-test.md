Files written:
- `dag/nodes/sec-six-functors/lem-coef-filtered-poset-cone-test.json`: statement, split in two proof steps, no new node and no Mathlib leaf.
- `citations.json`: four exact statement quotes for the two proof steps.

Attachments: none.

WANTED: Jacob Lurie, *Higher Topos Theory*, Remark 5.3.1.12 and Variants 4.2.3.15–4.2.3.16, for the converse reduction from poset nerves to arbitrary small simplicial diagrams. The PDF was read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf and is not archived under `literature/`.

The imported node was an earlier unsplit auxiliary copy from Q90; I retained its statement, source, blueprint ancestry, and seven recorded search results, and refreshed the required Q130 searches. No statement error or duplicate was found. No new node was created because both proof steps use only the two existing definition nodes and the cited HTT argument.

## Review by Q130

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, delivery-errors B–E, the chapter record `dag/chapters/sec-six-functors.json`, the unit `dag/units/sk-prop-sf-biduality-general.json`, the imported item copy, and the current statements of `def-coef-presentable-infinity-category` and `def-cbc-enhanced-diagrams-cones`. The item has no Lean declaration in either named source tree. Its statement matches HTT Remark 5.3.1.12: it includes the empty poset, requires no colimits, and uses the same definition of κ-filteredness.

Step 1 uses the presentable-category definition for κ-filteredness and the enhanced-diagram definition for coherent diagrams and cocones; those statements explicitly say that every κ-small coherent diagram admits a cocone and define coherent diagrams by simplicial maps. I checked the cardinal point that nondegenerate simplices of a poset nerve are finite chains and that an infinite regular κ bounds their number. The HTT nerve/join identification gives exactly the displayed extension.

Step 2 uses the same two statements for the converse conclusion. I checked the source route through Variants 4.2.3.15 and 4.2.3.16: arbitrary κ-small simplicial diagrams are reduced to the poset-nerve extension problems, and the compatible extensions glue to a coherent cocone. The empty-poset test supplies a vertex, so the nonemptiness clause is retained. I tested B empty, B a point, a two-point discrete poset, and a one-arrow poset; κ=aleph-zero; and E empty, terminal, and an ordinary nerve. The statement has no hidden colimit assumption or coefficient-category mismatch.

The item remains statement-only at the source level but is now marked `split` with a complete natural-language proof and exact citations. The Mathlib searches found only ordinary-category `IsCardinalFiltered` and inner-horn/quasicategory declarations, so there is no Mathlib match.

What could not be finished: no local HTT archive exists, so the source remains WANTED; no Lean or compiler work was performed under the stage-1 prohibition.

## Second reading by Q130

- Item statement: checked HTT Remark 5.3.1.12 (PDF p.400) against the displayed hypotheses and conclusion; the $|B|<\kappa$ formulation is equivalent to $N(B)$ being $\kappa$-small, the empty poset is retained, and no colimit hypothesis is present.
- Step 1: checked the finite-chain cardinal estimate against Definition 5.3.1.7 and the extension/cocone identification against `lem-coef-infinity-join-cocone-associativity`; the join gives exactly $N(B)\star\Delta^0=N(B^{\triangleright})$ with the prescribed restriction.
- Step 2: checked the converse against HTT Variants 4.2.3.15 and 4.2.3.16 and Remark 5.3.1.12; the cofinal map from a poset nerve is made explicit, its cocone restriction is justified by `lem-coef-infinity-cofinal-comma-criterion`, and the same apex is preserved.
- Existing definition nodes: `def-coef-presentable-infinity-category` and `def-cbc-enhanced-diagrams-cones` were reread in full; every cited clause (filteredness, coherent diagrams, and cocones) says what the steps use.
- Existing theorem nodes: `lem-coef-infinity-join-cocone-associativity` and `lem-coef-infinity-cofinal-comma-criterion` were reread in full; their hypotheses apply to the small nerves and cofinal map used here.
- New nodes: none; duplicate search over `dag/nodes` found no smaller existing criterion, and the two supporting facts are already DAG nodes.
- Edge cases: checked $B=\varnothing$, a one-point and two-point discrete poset, a one-arrow poset, $\kappa=\aleph_0$, an empty diagram, a terminal quasicategory, and the empty quasicategory. The empty-poset extension forces nonemptiness, while the empty quasicategory fails both sides.
- Changes: rewrote both proof steps to replace the unsupported “nerve/join model” and “variants glue” phrases by the exact join and cofinality arguments; added the two theorem dependencies, their verbatim citations, and the corresponding proof-dependency entries. No statement or source field was changed.
