1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-etale-coproduct-etale.json`: item, statement split in one step; no Mathlib leaf.
- `citations.json`: verbatim statement quotations for both cited nodes in step 1.

2. Attachments

None.

3. WANTED

None.

4. Problems found

No statement or blueprint error was found. The imported item had no proof; its proof now explicitly uses the existing coproduct-family statement and the existing etale-local-on-source result. No new node was needed, and no Lean declaration states the finite-family statement exactly.

5. Unfinished

Nothing.

## Review by M1

I read the item and its blueprint ancestor `lem-sc-etale-affine-qcoherent`, including the passage that forms the finite coproduct of an etale covering family. I checked the cited source as Stacks Morphisms, Definition 02GI and Lemma 02GJ (`lemma-etale-characterize`); the source says etaleness is local on an open cover of the source, which is exactly the argument used in the item. The item statement introduces the scheme, finite family, coproduct, and induced map and agrees with that source application, including the empty-family edge case.

For step 1, I opened `lem-weil-pbc-scheme-coproduct-family` and verified that its statement gives open immersions with pairwise disjoint images covering the coproduct and that each image is open and closed. I opened `lem-weil-pbc-etale-local-on-source` and verified that its statement gives the needed iff between etaleness of a morphism and etaleness of every restriction to a covering family of open source subschemes. The restriction identity `u \\circ \\iota_i=u_i` follows directly from the coproduct mapping property in the first cited statement, so the hypotheses of the locality lemma are met by the given etaleness of every `u_i`. The step is marked non-elementary because it invokes the cited locality theorem; only the restriction calculation and the vacuous empty-cover observation are elementary.

I searched the whole DAG and blueprint for the finite-coproduct etale assertion and for the locality fact before editing. The exact finite-family assertion was absent, while both cited statements already existed, so I created no duplicate helper node. I tested the argument on a one-member family (the induced map is the given etale map) and the empty family (the source is empty and the open-cover condition is vacuous). `citations.json` quotes the exact sentences used from both cited node statements.
