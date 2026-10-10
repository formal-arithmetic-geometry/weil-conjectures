# Stage 1 report: lem-pc-kflat-resolution

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-kflat-resolution.json` (item, split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-kflat-bounded-flat-replacement.json` (statement-only, no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-kflat-closure.json` (statement-only, no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-kflat-hocolim-truncations.json` (statement-only, no Mathlib match).

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` has the item's arbitrary-site hypotheses and conclusion exactly.

3. WANTED: none; the Stacks Project source is cited in the repository's citation index as Tag 06YS.

4. The item was unsplit and had no proof. I retained its statement and added the three strictly smaller lemmas needed by the Tag 06YS construction. Existing imported `lem-kun-*` nodes are restricted to schemes and constant coefficient sheaves, so they were not used for this arbitrary ringed-site statement. The Mathlib searches found only module-level flatness and generic quasi-isomorphism/truncation declarations, not the sheaf-level K-flat results.

## Review by M1

I read the item's source entry for Stacks Tag 06YS and checked that the statement introduces a site, a sheaf of commutative rings, an arbitrary complex, a flat-term K-flat complex, and a degreewise-surjective quasi-isomorphism. I also checked the neighboring definitions `def-pc-kflat-complex`, `def-pc-flat-sheaf-modules`, and `def-pc-quasi-iso-modules` for the meanings used in the statement. Step 1 cites the new bounded-above replacement statement verbatim and uses its functoriality for the truncation maps. Step 2 cites exactly the closure statement for bounded-above flat complexes, cones, countable sums, and flatness of sums; the degreewise-surjectivity observation is the direct component calculation for the cone and eventual truncation identity. Step 3 cites the new truncation/homotopy-colimit statement verbatim for both filtered-colimit preservation and the comparison with the original complex. Step 4 records the resulting conclusion and the elementary degreewise-surjectivity check. Each new node is statement-only, has a complete ringed-site context, a Stacks 06YS source place, and records the three required Mathlib searches with their actual no-match results. I tested the construction on a one-term complex and on the zero complex: the truncations stabilize and the cone construction gives the expected flat K-flat representative and degreewise surjection.

5. What I could not finish: no Lean implementation was written or built, as required for stage 1.

## Not duplicates

lem-pc-kflat-bounded-flat-replacement vs lem-pc-kflat-resolution: the new node treats only bounded-above input complexes, while the item asserts existence for every complex and adds the global homotopy-colimit construction.
lem-pc-kflat-bounded-flat-replacement vs def-pc-kflat-complex: the existing node defines K-flatness, whereas the new node asserts existence of a bounded-above flat replacement and a termwise surjective quasi-isomorphism.
lem-pc-kflat-bounded-flat-replacement vs lem-pur-integral-operations-well-defined: the existing node concerns invariance of integral pro-etale towers under K-flat resolutions, while the new node is the bounded-above replacement input on an arbitrary ringed site.
lem-pc-kflat-bounded-flat-replacement vs lem-kun-flat-resolution-existence: the existing node is restricted to small etale sites of schemes with constant coefficients and proves the full unbounded resolution, while the new node is the general bounded-above ringed-site replacement lemma.
lem-pc-kflat-bounded-flat-replacement vs def-weil-integral-derived-reduction: the existing node defines a particular completed-coefficient reduction, while the new node is an existence theorem for bounded-above flat complexes.
lem-pc-kflat-closure vs lem-pc-kflat-resolution: the new node gives only closure properties used inside the proof, while the item asserts a resolution of every complex and a quasi-isomorphism to it.
lem-pc-kflat-closure vs def-pc-kflat-complex: the existing node is a definition, while the new node proves closure of the defined class under cones and sums and flatness of sums.
lem-pc-kflat-closure vs lem-pur-integral-operations-well-defined: the existing node is a resolution-independence statement for completed operations, while the new node is a closure lemma for K-flat complexes on a ringed site.
lem-pc-kflat-closure vs lem-kun-flat-resolution-existence: the existing node is a scheme-etale full resolution theorem, while the new node supplies only the K-flat closure facts used by a homotopy-colimit construction.
lem-pc-kflat-closure vs def-weil-integral-derived-reduction: the existing node defines derived reduction, while the new node states no reduction operation and only concerns K-flat closure.
lem-pc-kflat-hocolim-truncations vs lem-pc-kflat-resolution: the new node only identifies the homotopy colimit of truncations with the original complex and filtered-colimit preservation, while the item additionally constructs flat K-flat terms and a surjection.
lem-pc-kflat-hocolim-truncations vs def-pc-kflat-complex: the existing node defines K-flatness, while the new node is a quasi-isomorphism theorem about truncation homotopy colimits.
lem-pc-kflat-hocolim-truncations vs lem-pur-integral-operations-well-defined: the existing node concerns independence of completed integral operations, while the new node concerns homotopy colimits and quasi-isomorphisms of arbitrary sheaf complexes.
lem-pc-kflat-hocolim-truncations vs lem-kun-flat-resolution-existence: the existing node proves a full scheme-etale flat resolution, while the new node is only the truncation/filtered-colimit comparison used in the general proof.
lem-pc-kflat-hocolim-truncations vs def-weil-integral-derived-reduction: the existing node defines reduction modulo a uniformizer, while the new node has no coefficient or reduction data and only states a homotopy-colimit comparison.

## Second reading by M1

- Item statement: checked against Stacks Project `sites-cohomology.tex`, Lemma 06YS (`lemma-K-flat-resolution`), hypothesis by hypothesis; the arbitrary ringed-site context, flat terms, K-flatness, quasi-isomorphism, and degreewise surjectivity agree.
- Step 1: checked against the construction following Lemma 06YS and the bounded-above replacement assertion; the functorial replacement and compatible truncation maps are the cited input.
- Step 2: checked against the homotopy-colimit cone construction in Lemma 06YS; cone/direct-sum K-flatness and flatness of direct sums are exactly the stated closure input, with degreewise surjectivity reduced to the eventual identity calculation.
- Step 3: checked against the filtered-colimit and truncation comparison used in Lemma 06YS; the cited statement supplies both quasi-isomorphism preservation and the truncation comparison.
- Step 4: checked as the direct conclusion of Steps 2 and 3; its degreewise-surjectivity assertion is elementary.
- `lem-pc-kflat-bounded-flat-replacement`: statement checked on the zero complex, a one-term flat complex, and a field-valued complex; context and all notions are self-contained and the source is 06YS.
- `lem-pc-kflat-closure`: statement checked on zero and one-term complexes and on countable direct sums; the closure claims match the cone construction used in 06YS and cite the K-flat and flat-sheaf definitions.
- `lem-pc-kflat-hocolim-truncations`: statement checked on the zero complex and a one-term complex (the truncations stabilize); the source comparison is 06YS and the filtered-colimit clause is the exactness input.

Changes made: corrected the item and auxiliary-node notion citations from K-flat/quasi-isomorphism misreferences to the cochain-complex, flat-sheaf, and quasi-isomorphism definition nodes; updated `stmt_deps` accordingly; refreshed verbatim citation quotes; retained the existing duplicate distinctions because the imported `lem-kun-*` statements are restricted to scheme etale sites.
