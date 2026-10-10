1. Files written:

- `lem-sc-smooth-proper-tensor-direct-sums.json`, statement split into three proof steps.
- `lem-pc-perfect-object-compact.json`, statement-only Stacks Tag 09M1 input; Mathlib no match.
- `lem-pc-proper-perfect-direct-image-perfect.json`, statement-only Stacks Tag 0B6G input; Mathlib no match.
- `citations.json`, verbatim statement excerpts for every cited node.

2. Attachments: none.

3. WANTED: none; the Stacks source was checked online at Tag 0A9R, and its cited inputs at Tags 09M1 and 0B6G.

4. No statement error was found. The imported item had no proof; its proof now follows the source's Hom calculation and perfect-generation argument. Searches of the whole DAG and blueprint found no existing node stating either auxiliary input. No Lean declaration with the item tag or theorem was found under `WeilConjectures/`.

5. I did not find a Mathlib theorem for either auxiliary input. The three required searches were run for each new node and recorded in its `mathlib_searches` field; LeanFinder returned only unrelated derived-category declarations, Loogle and Mathlib grep found no match.

## Review by E1

I read the item node, its blueprint ancestor `lem-sc-finite-duality`, and the Stacks Tag 0A9R page. The source states exactly the hypotheses used here: a perfect proper morphism of Noetherian schemes, a right adjoint to `Rf_*` on quasi-coherent derived categories, and the conclusion that the adjoint commutes with direct sums. I also checked the source statements for Tag 0B6G (perfect proper pushforward preserves perfectness) and Tag 09M1 (perfect objects are compact for quasi-compact, quasi-separated schemes), and recorded them as self-contained new nodes with all scheme and derived-category notions introduced through dependencies.

 Step 1 uses exactly the two new statements: Tag 0B6G supplies perfectness of `Rf_*P`, and Tag 09M1 supplies compactness and therefore the direct-sum Hom identity. Step 2 is the adjunction calculation displayed in 0A9R; it uses the same two statements only to justify the Hom direct-sum identity and the perfect test object. Step 3 uses the existing perfect-generation statement, whose conclusion explicitly gives closure under shifts, cones, retracts, and arbitrary direct sums. I checked the edge cases of an empty family and a singleton family: the canonical map is respectively the zero identity and the ordinary adjunction map. I corrected the imported empty proof by making the Hom calculation and generator argument explicit, and I kept all hypotheses of the item unchanged.

## Second reading by E1

- Item statement: checked against `duality.tex`, Lemma `lemma-proper-flat-noetherian` (Tag 0A9R), hypothesis by hypothesis; proper perfect morphism of Noetherian schemes, a right adjoint to `Rf_*`, and arbitrary set-indexed direct sums agree.
- Step 1: checked against Tags 0B6G and 09M1; derived direct image is perfect, then compactness gives the Hom/direct-sum isomorphism. Verdict: sound.
- Step 2: checked against the displayed adjunction calculation in Tag 0A9R; the canonical comparison map is carried to the compactness isomorphism. Verdict: sound and elementary from adjunction plus Step 1.
- Step 3: checked against the perfect-generator conclusion in Tag 0A9R and the existing perfect-generation node; the cone right-orthogonal argument now explicitly proves that the comparison map is an isomorphism. Verdict: repaired and sound.
- `lem-pc-perfect-object-compact`: checked against `perfect.tex`, Proposition `perfect-proposition-compact-is-perfect` (Tag 09M1), including empty-family and singleton cases; self-contained statement and three recorded Mathlib searches. Verdict: sound.
- `lem-pc-proper-perfect-direct-image-perfect`: checked against `more-morphisms.tex`, Lemma `more-morphisms-lemma-perfect-proper-perfect-direct-image` (Tag 0B6G); its Noetherian-base and perfect-proper hypotheses specialize exactly to the item. Verdict: sound.

Changes made: corrected all three source `place` fields to the exact Stacks labels; replaced the circular isomorphism-locus sentence in Step 3 with the cone/right-orthogonal generator argument; added the compactness citation used by that argument; updated `citations.json` accordingly.
