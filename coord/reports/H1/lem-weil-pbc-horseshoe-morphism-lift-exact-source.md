## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-horseshoe-morphism-lift-exact-source.json` — item split into four proof steps; no new nodes; Mathlib searches retain the recorded no-match/unavailable results.
- `citations.json` — verbatim statement quotes for every cited node in the four steps.

## Attachments

None.

## WANTED

WANTED: C. Weibel, *An Introduction to Homological Algebra*, Theorem 2.4.6 (the classical naturality calculation), for the exact-source horseshoe lift. The split is written from the Stacks 015I/013R construction and the explicit diagram chase.

## Review by H1

I read the item source description in `literature/stacks-project/derived.tex` (the comparison-morphism construction at Tag 015I, with Tag 013R for the null-homotopy input) and the existing statements of `lem-weil-pbc-ses-injective-kernel-splits`, `def-sp-injective-resolutions`, `def-sp-abelian`, and `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`. The item statement keeps all hypotheses: both source and target short exact sequences, exact augmented source rows, a target horseshoe, endpoint maps, and compatibility with augmentations.

Step 1 uses exactly the target-row splitting statement and the injective extension property; it does not assume that any source term is injective or that a source row splits. Step 2 uses only abelian exactness to factor the chain-map defect through the source C-row and the target A-row, and checks the augmentation defect at degree zero. Step 3 uses the exact augmented C-row to make the degree-minus-one augmentation complex acyclic, then applies the cited null-homotopy statement to the shifted bounded-below injective target. Step 4 is the direct substitution check that removes the defect and preserves both row maps and the augmentation, so it is marked elementary.

I checked the small concentrated-degree case (all differentials zero and identity endpoint maps): the construction gives the evident middle map after choosing the target splitting, and the correction term is zero. I also checked the zero source-row case, where all maps and defects vanish. The Mathlib search record was read as recorded in the item; no Mathlib theorem states this exact compatible middle-lift result. I corrected the imported metadata by setting `created.item` to this item, adding `lean_audit`, and making the split report explicit; no duplicate or auxiliary node was created because the cited nodes already provide the only external facts used.

## Not duplicates

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-horseshoe-morphism-lift`: the existing node requires all three source rows to be injective resolutions, while this item permits arbitrary exact augmented source complexes.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`: the latter is only the null-homotopy input; this item constructs a compatible middle morphism of short exact complexes.

## Second reading by H1

- Step 1 checked against Stacks `derived.tex`, Tag 015I's degreewise construction, and the statements of `lem-weil-pbc-ses-injective-kernel-splits` and `def-sp-injective-resolutions`; the target row splitting and injective extension hypotheses are present and the verdict is sound.
- Step 2 checked against the exact-row factorization in the Tag 015I/013T construction and `def-sp-abelian`; both defect factorizations and the augmentation comparison use the stated monomorphism, epimorphism, and exactness hypotheses, verdict sound.
- Step 3 checked against Stacks Tag 013R (`lemma-acyclic-is-zero`) and the displayed exact augmented C-row; adjoining C in degree -1 is acyclic, the shifted target is bounded below and termwise injective, and the sign conversion to `k` is correct, verdict sound.
- Step 4 checked by direct substitution in the definitions of a chain-map defect and the two short-exact rows; the correction cancels the defect and preserves both endpoint maps and augmentation, verdict elementary and sound.
- New nodes: none; every external fact is an existing DAG statement, and no Mathlib leaf or duplicate node is introduced.
- Statement and hypotheses checked against the item source description (Stacks `derived.tex`, Tags 015I and 013R) and the existing horseshoe-lift statement; zero source rows and concentrated degree-zero cases were tested and behave as claimed.

Changes made: no mathematical changes; added this second-reading record after the delivery preflight passed.
