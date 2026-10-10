Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ringed-spaces-derived-adjoint-general.json` (statement, split proof; Mathlib search found no exact match).
- No new nodes.

Attachments: none.

WANTED: none.

The item had no matching declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` (searched by item id, Tag 079W, and derived pullback/direct-image keywords). The existing node was unsplit and had an empty proof. I kept its statement and dependencies, filled its proof and split metadata, and left the imported `created` history unchanged.

## Review by J1

I read the item source citation, Stacks Tag 079W (the ringed-space derived adjunction), and the source passages for Tags 008A and 008Y that establish the underived tensor pullback adjunction. Step 1 uses the statements of `lem-pc-module-inverse-image-adjunction` and `lem-pc-module-change-of-rings-adjunction`; their statements provide exactly the inverse-image/direct-image and tensor/restriction Hom bijections needed, while `def-weil-pbc-topological-inverse-image` and `def-weil-sheaf-of-modules-category` provide the module structures and direct-image convention. Step 2 uses `lem-pur-derived-change-of-rings` for the everywhere-defined K-flat left derived functor, `def-pc-ringed-spaces-derived-direct-image` for the K-injective right derived functor, and the K-injective definition/existence nodes for the resolution hypotheses; it then applies the generic derived-adjunction statement `lem-sc-derived-adjunction-from-underived`. Step 3 takes only the Hom-bijection conclusion of that same node and substitutes the two derived-functor definitions. I checked that every cited node's statement contains the quoted fact in `citations.json`, that the derived comparison and resolution hypotheses are named, and that no new node duplicates an existing statement. The Mathlib searches were run with `msearch.py`: LeanFinder returned only generic underived adjunctions, Loogle was unavailable, grep found no derived ringed-space declaration, and LeanSearch was unavailable; these results are recorded verbatim in the node.

What I corrected: replaced the empty proof with the three source-aligned steps, set `status` to `split`, filled `split_report` and the missing audit metadata, and added the required citation quotes.

## Second reading by J1

- Item statement: checked against Stacks Tag 079W and the definitions of ringed spaces, sheaf-module categories, derived categories, and derived direct image; verdict: correct after adding the explicit ringed-space morphism and module-category citations.
- Step 1: checked against Tags 008A and 008Y and the statements of the inverse-image, change-of-rings, ringed-space, and sheaf-module nodes; verdict: correct after sourcing the structure map and the $g_*$ module action explicitly.
- Step 2: checked against Tag 079W and the K-flat/K-injective and generic derived-adjunction statements; verdict: the stated hypotheses and derived comparison data are present.
- Step 3: checked against the conclusion of `lem-sc-derived-adjunction-from-underived` and the two derived-functor definitions; verdict: elementary substitution and naturality argument.
- New nodes: none; the split uses existing nodes only and creates no duplicate or Mathlib-missing child.
- Changed the item statement citation to `def-weil-locally-ringed-space-morphism` and added the sheaf-module category context.
- Added Step 1 citations for the ringed-space structure map and the explicit $g_*$ module structure; synchronized `proof_deps` and `citations.json`.
