Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-tensor-action-naturality.json`: statement, split proof, no Mathlib leaf.
- `citations.json`: verbatim citations for all proof-step dependencies.

Attachments: none.

WANTED: `literature/stacks-project/more-algebra.tex`, Tag 06Y6 (lemma-derived-base-change), for the K-flat action, functoriality, and comparison-map paragraphs. The repository contains the citation metadata but not the Stacks source checkout.

## Not duplicates

`lem-pc-derived-tensor-action-naturality` vs `lem-pc-derived-tensor-transitivity`: the existing transitivity node gives a general tensor associativity/action/comparison theorem with an extra third algebra C; this item specializes to the balanced model with C = A tensor_R R' and records the chain map induced by F -> R'.

## Review by J1

I read the imported item, `lem-pc-balanced-derived-tensor-model`, `lem-pc-derived-tensor-transitivity`, and the ancestor `lem-pc-rf-perfect-base-change`. The item source is Stacks More on Algebra, Tag 06Y6. The source file is not present in this checkout, so the report records it as WANTED; the statements were checked against the imported Tag 06Y6 descriptions and the existing transitivity statement.

Step 1 uses the balanced-model statement for K-flat resolutions, the total-complex model, commuting R' actions, and independence/functoriality. The only additional operation is multiplication by a on P and the equality of the two scalar actions on pure tensors, which is the explicit chain-level calculation described in the step. The ring and complex hypotheses are those introduced by the item and by the cited balanced node.

Step 2 uses the affine comparison node's verbatim A' action and H^i(c) linearity clause, together with the balanced node's canonical resolution-independence and functoriality clause. This checks naturality in M and linearity under changing P or F without assuming a strict A' structure on the chain model.

Step 3 uses the balanced node for the model represented by P tensor_R F and the affine comparison node for the canonical derived comparison morphism. The map induced by F -> R' is the stated chain representative; associativity identifies P tensor_R R' with P tensor_A (A tensor_R R'). The quoted linearity clause gives A tensor_R R'-linearity on cohomology.

I searched the whole DAG for the Tag 06Y6/comparison-map and action keywords before deciding that no new support node was needed. I tested the construction on the zero complex and on the identity base-change case: the induced maps are respectively zero and the identity, and the scalar actions remain well-defined. The imported item had no proof; I supplied the three chain-level steps and added the existing affine comparison node to `stmt_deps`.

What was wrong or incomplete in the imported material: the item had an empty proof and omitted its dependency on the existing affine comparison statement. No source statement was changed, and no new node was created.

What remains unfinished: only the unavailable local Stacks source checkout, recorded above as WANTED; the DAG split and citation file are complete.

## Second reading by J1

- Item statement: checked against the imported Tag 06Y6 description and the balanced-model/transitivity statements; hypotheses on R, A, R', M, P, and F are explicit, and the zero-complex and identity-base-change cases behave as stated.
- Step 1: checked against `lem-pc-balanced-derived-tensor-model`; the A-action is supplied by multiplication on P and the commuting pure-tensor calculation is explicit.
- Step 2: checked against the action/naturality clause of `lem-pc-derived-tensor-transitivity` and the resolution-independence clause of the balanced-model node; comparison squares for multiplication by a and b are now written explicitly.
- Step 3: checked against the comparison-map clause of `lem-pc-derived-tensor-transitivity` and the balanced-model representation; the ordinary associativity identification and induced cohomology map are stated.
- New support nodes: none; the only node in the split is the item itself, so B1--B7 were checked on its self-contained statement, source tag, blueprint fields, and recorded Mathlib searches.
- Changes: corrected the item metadata's `created.item` to this item; replaced the Step 2 “transport” shortcut with the commuting-square argument; updated its citation to quote the transitivity naturality clause verbatim.
