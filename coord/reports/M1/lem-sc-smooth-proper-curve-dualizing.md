# Delivery report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-curve-dualizing.json`: item split into two steps; no Mathlib leaves.
   - `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-relative-dualizing-general.json`: new statement-only dependency; no Mathlib match.
   - `citations.json`: citation manifest for the non-elementary step.
2. Attachments: none. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag and relevant dualizing declarations found no declaration stating this item exactly.
3. WANTED: none. The cited Stacks source is recorded in the imported literature metadata; no additional source was needed.
4. Nothing in the item statement was changed. The original item had no proof, so I supplied the direct specialization route from the broader smooth-proper duality theorem. The new node is strictly broader (arbitrary Noetherian base and relative dimension), carries a statement only, and was searched in the whole DAG and blueprint before creation; no existing node states it.
5. I could not attach a Lean declaration: the source checkout has no declaration tagged `lem-sc-smooth-proper-curve-dualizing`, and Mathlib has no upper-shriek or dualizing-complex result matching the statement.

## Review by M1

I read the item source as Stacks Project, `duality.tex`, Tag 0BRT, Lemma 48.15.7, and checked the tag mapping in the Stacks tag index (`duality-lemma-smooth-proper`). The item statement is the specialization to a field base and relative dimension one. I also read the existing item and its ancestor `lem-sc-finite-duality`; the ancestor's route identifies the canonical sheaf with relative differentials, so this item supplies exactly that non-elementary input without citing the descendant trace node and creating a cycle.

Step 1 cites the new node's final sentence verbatim: it gives `f^! O_S` as the top exterior power of relative differentials shifted by the relative dimension. Its hypotheses explicitly include Noetherian base, smoothness, properness, and pure relative dimension, which specialize to `Spec k` and the given `g`. The definitions of smoothness, properness, derived direct image, and Kähler differentials are the item's statement dependencies. Step 2 uses no non-elementary fact: `wedge^1 M = M` and replacing `d` by `1` are defining identities.

For the new node I searched the DAG (`rg` for smooth proper dualizing, relative differentials, and upper-shriek terms) and the imported blueprint (`tools/blueprint_refs.py search`); no matching node or blueprint statement existed. I searched Lean source for the item tag and for dualizing declarations; no exact declaration was found. I recorded LeanSearch, LeanFinder, Loogle, and Mathlib-source grep results in `mathlib_searches`; all found no Mathlib upper-shriek/dualizing theorem. I tested the specialization on the identity morphism of `Spec k` (dimension zero analogue) and on `P^1_k -> Spec k` (dimension one), where the formula gives the expected shifted canonical sheaf. I corrected the initial plan by making the general theorem a statement-only node, rather than putting its proof inside the item or incorrectly citing the existing finite-duality trace node.
