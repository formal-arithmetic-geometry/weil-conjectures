# Delivery report: lem-weil-pbc-quasi-coherent-module-direct-sum

1. Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-quasi-coherent-module-direct-sum.json` (item; split, no new nodes).

2. Attachments: none.

3. WANTED: none. The Stacks source is present in `literature/stacks-project/modules.tex` and `schemes.tex`.

4. The imported node cited Schemes 01ID/01LA but did not record the primary Modules 01BF lemma and had no proof. I added the Tag 01BF source, cited the existing additive-category definition in the statement, and supplied a four-step proof. Step 1 checks the sectionwise binary sum is a sheaf and coproduct. Step 2 restricts to an affine open and uses the quasi-coherent affine counit. Step 3 transports the coproduct through the tilde functor and identifies the restricted sum with the tilde of the module direct sum. Step 4 applies the affine-local definition of quasi-coherence, including the empty-scheme edge case. Existing DAG nodes were searched by tag and concept; no duplicate or new auxiliary node was needed. Mathlib searches already recorded on the item found no closure theorem for quasi-coherence under biproducts/direct sums.

5. Nothing remains unfinished.

Blueprint reference: `blueprint.from.node` is `lemma-weil-pbc-h1-constructible-representation`, proof third paragraph (the finite-pushforward monomorphism into a direct sum); the route through the intermediate nodes is retained in `blueprint.from.via`. This item proves the binary quasi-coherent sum used by the quasi-coherent extension lemma in that route. Whole-blueprint searches with `tools/blueprint_refs.py search` for `quasi-coherent direct sum`, `quasi-coherent coproduct`, `quasicoherent biproduct`, `direct sum modules`, and `01BF`, plus an `rg` scan of the blueprint Markdown, found no blueprint node with the same statement, so `same_as` is `[]`.

## Review by E1

Read Modules Tag 01BF (the direct-sum lemma; proof omitted), Schemes Tag 01ID (affine direct sums of tilde modules), and Section 01LA item (3) (direct sums are quasi-coherent locally). The item statement agrees with 01BF, with the two sheaves and their sectionwise biproduct defined explicitly; the added `[def-weil-additive-category]` citation supplies the biproduct meaning. Each step was checked against the cited statements: Step 1 uses only sectionwise sheaf gluing and the biproduct identities; Step 2 uses the open-restriction preservation of quasi-coherence and the affine counit; Step 3 uses restriction preserving coproducts, the module direct-sum universal property, and the tilde left adjoint preserving colimits; Step 4 is the affine-neighbourhood definition. Only Step 4 is elementary; the other steps cite the stated non-elementary nodes. The existing-node search covered 01BF, 01ID, 01LA and direct-sum/biproduct terms across `dag/nodes`; no new node duplicates an existing fact. Hypotheses and edge cases checked: affine neighbourhoods exist for every point of a scheme, both module summands are quasi-coherent, restriction is along an open immersion, and the empty scheme satisfies the local condition vacuously. No worker repair was needed.
