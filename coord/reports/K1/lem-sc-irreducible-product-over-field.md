# Delivery report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-irreducible-product-over-field.json`: statement item, split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-product-irreducible-components-bijection.json`: statement-only unsplit node; no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The item had an empty proof despite being the irreducibility specialization of Stacks Tag 038F. I added the missing component-bijection dependency as a statement-only node and made the two proof steps explicit. No Lean declaration with the item tag or matching statement exists in slopmaster2.

## Review by K1

I read the item node and the already split dependent node `lem-sc-geometrically-irreducible-product`, whose Step 3 uses this item. I checked the source reference `literature/stacks-project/varieties.tex`, Tag 038F (the projection from a product with a geometrically irreducible factor induces a bijection on irreducible components), and retained the item's field, scheme, geometric irreducibility, fibre-product, and irreducibility hypotheses. I searched the whole DAG and blueprint for the component-bijection statement and found no existing node; the new node states that theorem self-containedly and cites the four notions it uses.

Step 1 cites the new node, whose statement verbatim supplies the projection and component bijection. Step 2 cites the definition of geometric irreducibility for the identity field extension and the irreducibility notion, then uses the elementary fact that a bijection with a singleton gives a singleton. I checked the edge cases `K'/K` equal to the identity and either factor `Spec K`; the conclusion is immediate in both. Mathlib searches (LeanSearch, Loogle, and source grep) found only `Scheme.Hom.irreducibleComponentsEquiv` under an additional open-map hypothesis, so neither node is a Mathlib leaf.
