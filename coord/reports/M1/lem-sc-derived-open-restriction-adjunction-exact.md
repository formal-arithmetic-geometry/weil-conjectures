Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-open-restriction-adjunction-exact.json` (item, split)
- no new nodes (the extension-by-zero assertion is a clause of the item and is proved directly in its second step)

Attachments: none.

WANTED: none.

The item has no sorry-free declaration in the Lean source. I checked the existing DAG nodes for scheme-module extension by zero, Zariski abelian sheaves, localized sites, and the opposite restriction/direct-image adjunction; none states the arbitrary ringed-space module result. The extension-by-zero argument follows Stacks Sheaves Lemma 00A7 and Modules Lemma 01AK directly in the item, since it is a clause of the item rather than a separate node. Step 1 uses the existing ringed-space stalk exactness criterion (01AG(5)) and verifies that neighbourhoods inside the open are cofinal, so restriction preserves stalks and exactness. I recorded all citations in `citations.json` and ran the required Mathlib searches; only generic sheafification, scheme, and abelian infrastructure appeared.

## Not duplicates

lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-module-extension-by-zero-adjunction: the existing node assumes a scheme and states the scheme-module construction with stalks; this item is for an arbitrary ringed space and also includes exactness of restriction and extension by zero.

lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-module-open-restriction-injectives: the existing node is a scheme-specific injective-resolution consequence, while this item is the underlying arbitrary-ringed-space adjunction and exactness statement.

lem-sc-derived-open-restriction-adjunction-exact vs lem-weil-pbc-zariski-extension-by-zero-adjunction: the existing node concerns abelian sheaves on the Zariski site, while this item concerns modules over an arbitrary sheaf of rings on a ringed space.

## Review by M1

I read the item source (Cohomology Lemma 08BS) and the extension-by-zero sources (Sheaves 00A7 and Modules 01AK), and checked the existing statements of every cited DAG node. The first item step uses the exact stalkwise criterion from `lem-weil-pbc-module-stalk-exact` and the short-exact-sequence notion from `def-weil-pbc-exact-sequence`; the open restriction identifies stalks because open neighbourhoods are cofinal. The second step constructs the presheaf, uses module sheafification for the natural adjunction, derives the stalk formula from cofinal neighbourhoods and stalk invariance under sheafification, and proves exactness stalkwise using the same criterion. I corrected the initial plan by removing a child node that merely restated a clause of the item, and documented why the scheme, injective-resolution, and Zariski-abelian nodes are not duplicates.

## Second reading by M1

- Item statement: checked against Cohomology tag 08BS / `cohomology-lemma-restrict-K-injective-to-open`; the ringed-space, open-subspace, adjunction, and exactness hypotheses and conclusions agree.
- Step 1: checked against Modules tag 01AG / `modules-lemma-abelian` (stalkwise exactness) and the definition of short exactness; cofinal neighbourhoods preserve each stalk, including the empty-open and zero-sequence cases.
- Step 2: checked against Sheaves tag 00A7 / `sheaves-lemma-j-shriek-modules` (presheaf construction, adjunction, and stalks), Modules tag 01AK / `modules-lemma-j-shriek-exact` (underlying abelian exactness), and the cited sheafification/stalk nodes; the stalk is zero outside $U$ and unchanged inside $U$, so the zero module and field cases behave correctly.
- New nodes: none; the removed proposed child was only a restatement of the item clause, and all remaining dependencies are existing nodes searched by id and key words.
- Form audit: the item is self-contained, TeX is escaped once, all notions cite definition nodes, and the corrected `created.item` now names this item.
- Changes: repaired `created.item` from `lem-sc-derived-k-injective-restrict-open` to `lem-sc-derived-open-restriction-adjunction-exact`; added this source-by-source second-reading record. No mathematical statement or proof step required weakening.

