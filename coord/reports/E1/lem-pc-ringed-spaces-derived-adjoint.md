# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-ringed-spaces-derived-adjoint.json`: statement node, split proof, no new nodes.
- `citations.json`: verbatim statement excerpts for every proof citation.

## Attachments

None. The slopmaster2 declaration `AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction` is narrower (étale sheaves with coefficient-category hypotheses) and does not state this ringed-space item exactly.

## WANTED

None. The source is the locally cited Stacks Project result Tag 079W.

## What I checked

I read the imported item, its unit and chapter records, and the neighboring composition item. The item's statement agrees with Stacks, Cohomology Lemma 079W: it is the unbounded derived adjunction for a morphism of ringed spaces, specialized here to schemes. I also read the source declarations for `def-pc-derived-pullback`, `def-pc-derived-direct-image`, `def-pc-derived-category`, and `lem-pc-module-pullback-adjunction`.

Step 1 uses the module-pullback node for the underived Hom bijection and quotes its conclusion verbatim; the two definition nodes supply that the displayed functors are the left and total right derived functors. Step 2 uses the same underived adjunction together with the K-flat resolution clause of the pullback definition, the total-derived-functor clause for direct image, and the derived-category definition. I checked that the K-flat/K-injective resolution argument is precisely the construction in Tag 079W and that it gives the displayed Hom sets on the unbounded derived categories. Step 3 uses the naturality clause of the underived adjunction and the derived-category construction; the resolution maps and localization maps are functorial, so the resulting bijection is bifunctorial.

I searched for existing DAG statements by the Stacks tag and by the derived-adjunction terms. The existing `prop-weil-pbc-derived-inverse-image-adjunction` is only bounded-below étale sheaves, and the existing module pullback node is underived, so neither duplicates this item. Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder found the abstract `CategoryTheory.Adjunction.derived`, while Loogle and grep found no exact ringed-space derived declaration and LeanSearch was unavailable. The abstract result is not an exact instantiation of this item's ringed-space definitions, so no Mathlib leaf was added.

## Review by E1

I checked each step against the source and opened every cited node. Step 1 takes exactly the underived pullback/direct-image Hom bijection from `lem-pc-module-pullback-adjunction`; it does not treat a definition node as a theorem. Step 2 explicitly identifies the K-flat and K-injective resolution mechanism and cites the definitions that introduce the derived functors and the ambient derived categories. Step 3 takes only naturality of the same underived bijection and the functoriality of localization. I verified the edge cases conceptually: for the identity morphism the construction reduces to the identity adjunction, and for the zero complex both Hom groups are singleton sets. I corrected the imported empty proof by adding these three source-based steps, keeping the statement unchanged, and recorded exact citation quotes in `citations.json`.

## What was wrong or incomplete

The imported node had no proof, no proof dependencies, and no split report. The source checkout has a concrete étale derived-adjunction declaration, but its hypotheses do not match the item's general ringed-space statement; it is therefore not an attachment.

## Could not finish

Nothing remains for this stage-1 split.

## Second reading by E1

- Item statement: checked against Stacks `cohomology.tex`, Tag 079W (`lemma-adjoint`), hypothesis by hypothesis; narrowed the wording to the scheme setting used by the cited definition nodes.
- Step 1: checked against Stacks Tags 079W and 0096 and opened `lem-pc-module-pullback-adjunction`, `def-pc-derived-pullback`, and `def-pc-derived-direct-image`; the underived adjunction and the two derived-functor identifications are exactly what the cited statements provide.
- Step 2: checked against the proof of Tag 079W and `def-pc-derived-category`; replaced the unsupported resolution-level narration with the source's formal derived-adjunction argument applied to Step 1.
- Step 3: checked against the bifunctoriality clause of Tag 079W and the naturality sentence in `lem-pc-module-pullback-adjunction`; the cited statements support naturality in both variables.
- New nodes: none; B1--B7 and duplicate/search checks are vacuous for this split.
- Changes: removed the unsupported parenthetical generalization to arbitrary ringed spaces, aligned Step 2 with the actual one-line source proof, and corrected the sandbox `created.item` metadata to this item.
- Small cases checked: identity morphism gives the identity adjunction; zero complexes give singleton Hom sets; the empty scheme and field cases introduce no extra hypotheses.
