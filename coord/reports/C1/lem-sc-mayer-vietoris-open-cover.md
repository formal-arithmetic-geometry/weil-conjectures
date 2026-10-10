# Stage 1 report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-mayer-vietoris-open-cover.json`: item split, one proof step, no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-sc-mayer-vietoris-ringed-space.json`: new statement-only node, no Mathlib leaf.
- `citations.json`: one verbatim citation for the item step.

2. Attachments: none.

3. WANTED: none. Stacks Project `cohomology.tex`, Lemma 01EB is present in `literature/stacks-project/`.

4. Checks and corrections: I read the item source and its imported statement, and searched the whole DAG and blueprint for a ringed-space or scheme-module Mayer–Vietoris node. The only nearby result is the etale-site node `lem-weil-pbc-etale-mayer-vietoris`, whose hypotheses and cohomology theory do not apply here. I also searched the Lean source for the item id, 01EB, 09MR, and Mayer–Vietoris names; there is no declaration stating this item without `sorry`. The new node states the full fact taken from 01EB, including the restriction naturality used by the item's conclusion. The item's single step specializes it to the open subscheme W and quasi-coherent module F, and uses exactly the quoted sentence of the new node. I checked edge cases conceptually: U=W gives the identity restriction sequence with a zero V contribution, U∩V empty gives the expected direct sum restriction map, and W'=W recovers the original sequence. Mathlib searches were run for both nodes with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as unavailable. Mathlib's hits are generic site or topological-sheaf Mayer–Vietoris constructions, not this O_X-module cohomology theorem.

5. Nothing remains unfinished in the split. The new node is intentionally statement-only and joins the downstream queue as required.

## Review by C1

I checked `literature/stacks-project/cohomology.tex` at Lemma 01EB and read the item statement against that lemma. The new ringed-space node states the exact long sequence, its restriction/difference maps, naturality in the module, and the restriction-to-an-open compatibility. The item step cites that node for all of these facts; its hypotheses specialize by taking the ringed space to W, the cover to U and V, and the module to F. The quasi-coherent hypothesis is preserved under restriction and does not add an unlisted theorem to the step. I verified that no cited node is being used for a fact absent from its statement, and the quote in `citations.json` is copied verbatim. I checked the small cover cases U=W, empty intersection, and W'=W for the direction of the restriction and difference maps. No statement or source correction was needed.
