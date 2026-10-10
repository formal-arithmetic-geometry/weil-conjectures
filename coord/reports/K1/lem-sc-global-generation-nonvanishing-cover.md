# Delivery report

1. Files written:
   - `item.json`: `lem-sc-global-generation-nonvanishing-cover`, statement, split proof; no new nodes.
   - `citations.json`: two verbatim node-statement quotes for step 1.
2. Attachments: none for this item. The existing `def-sc-invertible-module` and `def-weil-pbc-generating-sections` nodes were used as written.
3. WANTED: none.
4. No statement or blueprint error was found. The imported item had an empty proof; I supplied the local stalk argument following Modules 01AM/01CY and Sheaves 0H7H(2). No extra helper node is needed: invertibility supplies a local rank-one basis, and the generating-sections definition supplies the finite local expression whose reduction modulo the maximal ideal has a nonzero summand.
5. Nothing remains unfinished.

## Review by K1

I read the item and its ancestor reference, the chapter/unit context, the existing definition nodes, and the relevant source references in `literature/stacks-tags-cited.tsv` and the Stacks-based node records. I also searched the full DAG, blueprint references, and `WeilConjectures` for an exact declaration or duplicate split; none exists. The sole proof step cites `def-sc-invertible-module` for a local rank-one basis and `def-weil-pbc-generating-sections` for local finite expressions by generating global sections; both cited statements explicitly provide those facts. The remaining passage to stalks and reduction modulo the maximal ideal is the one-line module calculation underlying 01CY/0H7H(2), and the conclusion is exactly the definition of the nonvanishing locus. I checked the edge cases of the empty scheme (empty union), the trivial line bundle (section 1), and a one-point scheme. Mathlib searches already recorded on the item found no matching theorem, so the item remains a non-Mathlib split statement.
