Files written:

- `dag/nodes/sec-picard-framework/lem-pc-restrict-derived-direct-image-open.json`: item split, no new nodes, Mathlib searches recorded.
- `citations.json`: verbatim quotes for both proof-step dependencies.

Attachments: none. No WANTED items.

The source Lean declaration `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict` was checked in `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean:421-429`; it still contains `sorry` and only states a degreewise higher-direct-image variant, so it is not an attachment. The existing DAG nodes `lem-sc-derived-k-injective-restrict-open` (Stacks 08BS) and `def-pc-ringed-spaces-derived-direct-image` were read in full. Step 1 uses exactly the former node's assertion that termwise restriction of a K-injective complex along an open inclusion remains K-injective. Step 2 uses exactly the latter node's K-injective model for derived direct image, then checks on each open W of V that both direct-image complexes evaluate to `I^\\bullet(f^{-1}(W))`; the equality is compatible with differentials and natural in E. The hypotheses U=f^{-1}(V), g:U\\to V, and the open inclusion required by 08BS were verified from the item's statement. The item itself had only a LeanFinder search originally; I added the executed Loogle, grep, and unavailable LeanSearch records. No new node was created because the only non-elementary input is already present in the DAG.

## Review by H1

I checked the item against Stacks Cohomology Lemma 08FE and its proof dependency Lemma 08BS. The K-injective restriction claim is supplied by `lem-sc-derived-k-injective-restrict-open`, whose statement matches the first step verbatim in substance. The derived-direct-image construction is supplied by `def-pc-ringed-spaces-derived-direct-image`; its statement explicitly says that a K-injective resolution computes the derived pushforward, which is the only fact used in step 2. I checked the open-preimage hypothesis and the induced morphism before applying 08BS. The remaining equality is a sectionwise identity on opens, so no additional node or hidden hypothesis is required. I also checked the small edge case V=Y, where U=X and the canonical map is the identity, and V=empty, where both restricted complexes are zero. The split metadata, blueprint reference, searches, and citation quotes were written after these checks.

## Second reading by H1

- Item statement: checked against `cohomology.tex`, Lemma `lemma-restrict-direct-image-open` (Tag 08FE), lines 7901-7905; the ringed-space morphism, open subspace, induced morphism, derived-category object, and restriction/direct-image conclusion agree hypothesis by hypothesis.
- Step 1: checked against the proof of Tag 08FE and the statement of `[lem-sc-derived-k-injective-restrict-open]` (Tag 08BS); the preimage of an open is open, and the cited node supplies preservation of K-injectivity under termwise restriction. Verdict: correct; no elementary claim is hidden.
- Step 2: checked against lines 7908-7915 of Tag 08FE and `[def-pc-ringed-spaces-derived-direct-image]`; the cited definition supplies the K-injective model, while the displayed equality on each open `W` is the direct-image definition and is compatible with restrictions and differentials. Verdict: correct; naturality follows componentwise from the same restriction maps.
- New nodes: none; therefore B1-B7 and duplicate/Mathlib-leaf checks are vacuous. The two cited nodes were searched in the DAG and read in full; neither is a restatement of this item.
- Mathematics checks: `V = Y` gives `U = X` and the identity restriction; `V = empty` gives the zero restricted complexes; for a one-point space over a field the sectionwise equality is literal. No extra flatness, quasi-compactness, or separatedness hypothesis is used.
- Changes made: added this second-reading record to satisfy the delivery contract; no statement, proof step, citation quote, or search result required mathematical repair. The source distinction was checked explicitly: 08FE is the ringed-space lemma in `cohomology.tex`, while 0D6G is the separate ringed-sites analogue in `sites-cohomology.tex`.
