Files written:

- `dag/nodes/sec-picard-framework/lem-sc-exterior-top-direct-sum.json`: item, statement split into three proof steps; no Mathlib match for the top-degree direct-sum isomorphism.
- `dag/nodes/sec-picard-framework/lem-sc-tensor-product-free-basis.json`: new statement node, Mathlib match `Module.Basis.tensorProduct` and `Module.Basis.tensorProduct_apply`.
- `citations.json`: verbatim statement excerpts for every cited node in every step.

Attachments: none.

WANTED: none.

## Review by J1

I read the item source route in `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/_section.md` and the determinant paragraph represented by the imported blueprint node `lem-sc-riemann-roch`. The item statement keeps the commutative-ring, finite-basis, exterior-power, tensor-product, canonical-map, and naturality hypotheses exactly. I also read the existing Mathlib-leaf node `lem-weil-pbc-exterior-power-free-basis`, whose statement supplies the wedge bases and the rank-zero conventions used in the proof.

Step 1 cites that exterior-power basis statement and the new `lem-sc-tensor-product-free-basis`; their statements explicitly say that the listed wedges and product tensors are bases. The definition citations state what free modules, exterior powers, and tensor products are, so the basis calculation is made in the same objects as the item. I checked the new node against `Mathlib/LinearAlgebra/TensorProduct/Basis.lean`, where `Module.Basis.tensorProduct` constructs the product basis and `tensorProduct_apply` identifies its vectors. I recorded LeanSearch, Loogle, and source grep searches for this node, and searched the DAG and blueprint for an existing tensor-product-basis node before creating it.

Step 2 uses exactly those two basis statements to show that the alternating map sends each source basis vector to the corresponding target basis vector, hence is an isomorphism. The exterior-algebra statement supplies multilinearity and alternation, and the tensor-product universal property supplies the unique linear extension. These are the facts quoted in `citations.json`; no step relies on a proof body of a cited node.

Step 3 uses the multilinearity/alternation and tensor universal-property clauses to explain basis independence and naturality under module isomorphisms. I marked this short compatibility check elementary because it is the direct functoriality calculation from those definitions. I checked ranks $(0,0)$, $(1,0)$, $(0,1)$, and $(1,1)$: the map is respectively the identity on $R$, the evident identification with $M$ or $N$, and the usual two-factor wedge ordering. The blueprint references are filled from `lem-sc-riemann-roch`, with the item’s determinant-paragraph place and the new node’s more precise tensor-basis place.

What was wrong or incomplete in the imported item was only that it had no proof split and its Mathlib searches did not record the tensor-basis dependency. No statement error or source error was found.

What remains unfinished: no Lean code is written at stage 1; the natural-language node and its citations are complete.
