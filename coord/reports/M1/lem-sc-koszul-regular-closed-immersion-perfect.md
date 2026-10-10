Files written:

- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-closed-immersion-perfect.json` (statement, split; no new nodes)
- `citations.json` (verbatim citations for all proof-step uses)

Attachments: none.

WANTED: `literature/stacks-project/more-on-morphisms.tex`, Tag 068C, Lemma 37.61.7, because the Stacks source files are not present in this checkout. The split follows the imported source citation and the node definitions.

No new node was needed. The Koszul homology assertion is the definition of Koszul-regularity; the degree-zero quotient calculation and finite-free boundedness are elementary consequences of the cited Koszul-complex definition. The affine quotient description is part of the cited closed-immersion definition. No source statement was changed.

## Review by M1

I searched the Lean source checkouts for the item id, its blueprint tag, and the terms “Koszul regular”, “perfect immersion”, and “Koszul”; there is no sorry-free declaration stating this item. I read the item statement, its cited definitions, and the imported Tag 068C source reference. Step 1 uses exactly the affine Spec and quotient description in `def-weil-closed-immersion`, under the scheme and closed-immersion hypotheses. Step 2 uses the definition's vanishing of nonzero Koszul homology and the Koszul complex's degree-zero term and differential; the calculation that the image of d1 is the generated ideal is elementary. Step 3 uses the finite-free exterior-power terms and the definition of a locally perfect complex. I checked the empty sequence case (the Koszul complex is A in degree zero) and the principal case (A -> A has cokernel A/(f)); both support the quotient and perfectness conclusions. Mathlib searches were run for LeanFinder, Loogle, grep, and LeanSearch; the first three found no matching theorem and LeanSearch was unavailable, recorded as such in the node.

## Second reading by M1

Source checked: Stacks Project Tag 068C, Lemma 37.61.7, and its definitions in Tag 0687, Definition 37.61.2, and Tag 068Y, Lemma 15.84.2. The local `.tex` files are absent from this checkout, so I read the tagged Stacks pages directly. Tag 068C assumes no Noetherian hypothesis and proves perfection of the morphism, not merely perfection of its pushed-forward structure sheaf; Tag 0G2E, Lemma 37.61.12, supports the additional pushforward conclusion. The item now has both conclusions, with the correct affine-local hypotheses and no Noetherian assumption.

- Step 1: checked against `def-weil-closed-immersion` and the affine reduction of 068C; the quotient description is exact, and restriction of the pushforward is the sheaf of A/I. Pass after adding the citation and affine-section calculation.
- Step 2: checked against `def-weil-pbc-koszul-regular-sequence` and `def-weil-pbc-koszul-complex`; their statements give vanishing, K_0=A, K_1=A^r and d_1(e_i)=f_i. The quotient homology, augmentation and localization check are elementary. Pass after adding both citations and the calculation.
- Step 3: checked against the finite exterior-power basis clause of `def-weil-pbc-koszul-complex` and the affine-cover criterion of `def-pc-perfect-complex`; finite freeness, boundedness and the sheafified resolution give the stated pushforward conclusion. Pass after adding both citations.
- Step 4: checked against the new `def-sc-perfect-closed-immersion` and 068C/068Y; the resolution from Step 3 meets the local criterion for the immersion itself. Pass. Empty Y is vacuous, r=0 gives A in degree zero, r=1 gives A -> A with positive homology zero exactly when f_1 is injective; a field and the unit ideal give the expected zero quotient.
- New node `def-sc-perfect-closed-immersion`: checked against 0687 and 068Y, with 0G2E confirming the quotient-resolution characterization for closed immersions. It states only a self-contained definition, cites the scheme, closed-immersion, affine-spectrum and projective-module notions, uses singly escaped TeX, and gives tags and labels in `source`. Whole-blueprint searches for `perfect morphism`, `perfect closed immersion` and `068Y`, plus node searches for those terms, found no existing definition. LeanFinder, Loogle and two Mathlib greps found no matching declaration; all queries were run and logged. Pass.

Changes: removed the unsupported Noetherian hypothesis; separated perfectness of the immersion from perfectness of its pushforward; added the missing definition node, Koszul-complex dependency, step citations and verbatim citation quotes. The first report's WANTED note describes its earlier environment; the tagged source was available online for this reading.
