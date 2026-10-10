# Delivery report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-sc-product-irreducible-components-bijection.json`: statement node, split into two proof steps; Mathlib searches remain no-match.
   - `citations.json`: six verbatim node-statement citations for the two steps.
2. Attachments: none. No sorry-free declaration for the item was found in `WeilConjectures/`.
3. WANTED: `literature/stacks-project/varieties.tex`, Tag 038F full proof text; the repository contains the citation index but not the source file, so the proof expansion is recorded as agent-written from the cited lemma.
4. The imported node was unsplit and had no proof. I preserved its statement, dependencies, source tag, and blueprint reference, and added the forward component construction and inverse maximality argument from Tag 038F. Searches across the DAG and blueprint found no duplicate theorem or smaller node to cite; the Lean source has no matching declaration.
5. Nothing remains unfinished in the split; the external Stacks proof text is unavailable in this checkout (reported above).

## Review by M1

I read the target node, its blueprint ancestor `thm-sc-jacobian-representability`, the unit record `sk-prop-jacobian`, and the neighboring consumers `lem-sc-irreducible-product-over-field` and `lem-sc-geometrically-irreducible-product`. I searched the whole DAG and blueprint for Tag 038F, the component-bijection wording, and likely Lean names; only this unsplit item and its consumers appeared. I also searched `WeilConjectures/` for the item id, the blueprint tag, and product/component terminology; no declaration states it.

Step 1 uses the exact statements of `def-pc-geometrically-irreducible` (irreducibility after every field extension), `def-weil-scheme-over-base` (schemes and structure morphisms), `def-pc-fibre-product` (the product and projections), and `def-weil-irreducible-components` (maximal irreducible closed subsets). These citations support forming the inverse image over a component and taking its irreducible closure. Step 2 uses the component maximality statement and the fibre-product projection; it identifies the image component and proves the two constructions are inverse. The steps are non-elementary because they are the substance of Tag 038F, rather than one-line consequences of the definitions. Every cited node is listed in `proof_deps`, and every citation quote is copied verbatim into `citations.json`.

I checked the hypotheses explicitly: `K` is a field, `U` is geometrically irreducible, `V` is an arbitrary `K`-scheme, and the product is over `Spec K`; no quasi-compactness, separatedness, or nonemptiness hypothesis was added. The edge cases `U = Spec K` and `V = Spec K` reduce to the identity correspondence on components, while an empty `V` has no irreducible components on either side. The only correction to the imported node was adding the missing proof and its dependency accounting; the statement and blueprint fields were unchanged.
