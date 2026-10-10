# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-object-compact.json` — statement split, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim citations for all three proof steps.

Attachments: none.

WANTED: none.

The item was not present as a declaration in either Lean source checkout. I checked the item against Stacks `perfect.tex`, Proposition `proposition-compact-is-perfect` (Tag 09M1), and retained only its forward implication. The imported statement is unchanged. The existing DAG node `lem-pc-perfect-tensor-hom-duality` supplies the duality isomorphism, while `lem-pc-derived-direct-image-preserves-direct-sums` supplies the global-sections comparison through the structure morphism. `lem-pc-derived-qcoh-direct-sums` records existence of the required coproducts. No new node was created because the tensor/direct-sum calculation is a direct termwise argument from K-flat models and definitions.

## Review by C1

I read the Tag 09M1 proposition and its proof in `/home/ubuntu/c1-stacks-review/perfect.tex` (the forward paragraph beginning with the perfect dual `K^\\vee`). Step 1 uses exactly the tensor-Hom isomorphism stated by `lem-pc-perfect-tensor-hom-duality`, with `A=\\mathcal O_X`; the identification with `H^0` is the definition of derived global sections. Step 2 uses only the existence of set-indexed sums in `D_{\\mathrm{QCoh}}` from `lem-pc-derived-qcoh-direct-sums` and spells out the K-flat termwise tensor calculation, so it is marked elementary. Step 3 applies the statement of `lem-pc-derived-direct-image-preserves-direct-sums` to the quasi-compact, quasi-separated structure morphism and takes degree-zero cohomology, yielding the required Hom comparison. I checked the empty family as well as ordinary families. The Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such in the item metadata.

## Second reading by C1

- Statement: checked hypothesis by hypothesis against Stacks Tag 09M1, Proposition `proposition-compact-is-perfect`; the retained perfect-implies-compact direction is exact, with all notions supplied by the listed definition nodes.
- Step 1: checked against Tag 09M1's first paragraph and the statement of `lem-pc-perfect-tensor-hom-duality`; the specialization `A=\\mathcal O_X` and the degree-zero derived-global-sections identification are valid under the stated QCoh hypotheses.
- Step 2: checked against Tag 09M1's assertion that derived tensor with the dual commutes with direct sums; the K-flat replacement, QCoh coproduct, and total-tensor construction are now explicitly cited by `lem-pc-kflat-resolution`, `lem-pc-derived-qcoh-direct-sums`, and `def-pc-tensor-complex-sheaves`, with the remaining reindexing argument elementary.
- Step 3: checked against Tag 09M1 and `lem-pc-derived-direct-image-preserves-direct-sums`; the structure morphism to `Spec(\\mathbb Z)` is qcqs, and taking `H^0` gives exactly the compactness comparison.
- New nodes: none; there were no new statements to audit under B1--B7. I searched for existing tensor/direct-sum and derived-global-sections nodes and retained the existing statements rather than creating duplicates; the duplicate direct-image node was also checked and not cited.
- Edge cases: the empty family, singleton family, the zero complex, a field-valued affine scheme, and the empty scheme all make the displayed comparison the expected identity or zero isomorphism.
- Changes: repaired Step 2's missing K-flat and total-tensor dependencies and added verbatim citations for those nodes; no statement or source was changed.
