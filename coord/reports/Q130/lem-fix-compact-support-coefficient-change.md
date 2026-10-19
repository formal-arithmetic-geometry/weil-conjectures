1. Files written

- `dag/nodes/sec-smooth-purity/lem-fix-compact-support-coefficient-change.json`: repaired item, with the statement and Lean record unchanged and the former long pullback step split into five short steps (steps 8–12), followed by the unchanged counit step 13.
- `dag/nodes/sec-smooth-purity/lem-fix-direct-image-scalar-exchange.json`: new statement-only lemma for the proper/direct-image exchange cube; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-fix-open-scalar-exchange.json`: new statement-only lemma for the open scalar/base-change square; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-fix-site-open-exchange.json`: new statement-only lemma for etale/pro-etale site comparison of the normalized open square; Mathlib searches found no match.
- `citations.json`: exact witnesses for every non-elementary citation in all 13 item steps.
- `searches.jsonl`: retained command logs for the item and all three new nodes.

2. Attachments

None. I searched the slopmaster2 `WeilConjectures/` source by the exact item id, declaration names, and compact-support/coefficient terminology. The existing `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_comp_iso` only assumes coefficient compatibilities and asserts existence; it does not prove this item or its compatibility clauses.

3. WANTED

None. All cited source documents are present.

4. What was wrong or needed attention

The maintainer returned the previous delivery because its pullback-compatibility step had 3669 characters and hid several independent lemmas. I kept the item statement, route, and Lean record unchanged. I extracted the proper direct-image exchange, open scalar exchange, and etale/pro-etale open site-comparison exchange as three new statement-only nodes, and used the existing transport-identifies-exchange node for the remaining transport lemma. The item now has short steps for defining the ambient exchange, applying each extracted lemma, concatenating the squares, and identifying the geometric exchange on the witnessed domain. No new node duplicates an existing DAG statement: searches by the relevant exchange and site-comparison terms found only the item and generic mate/tensor nodes, which are cited as tools.

The new nodes are intentionally unsplit statement obligations: each states a genuine derived categorical compatibility with its own objects, hypotheses, and source place, rather than restating a clause of the item. Their Mathlib searches used LeanFinder, LeanSearch, Loogle, and Mathlib grep; LeanSearch was rate-limited and is recorded as unavailable in `mathlib_searches`.

5. Unfinished

Nothing in this one-level repair. No Lean file was written or compiled.

## Not duplicates

lem-fix-direct-image-scalar-exchange vs lem-weil-pbc-square-iso-pasting: states pasting identities only for inverse-image isomorphisms on etale abelian sheaves; the new node compares derived direct-image exchanges across a coefficient ring map on pro-etale module categories.

lem-fix-direct-image-scalar-exchange vs lem-weil-pbc-derived-square-iso-pasting: states pasting for bounded-below etale inverse-image comparisons at fixed coefficients; the new cube includes unbounded pro-etale scalar extension and direct-image mates.

lem-fix-direct-image-scalar-exchange vs lem-weil-pbc-mate-pasting: gives abstract two-square mate identities; it does not identify the canonical scalar/inverse-image cube or assert the displayed equality of its four geometric/coefficient exchange maps.

lem-fix-direct-image-scalar-exchange vs lem-kun-derived-exchange-cube: has only scheme-map faces and bounded-below etale abelian sheaves; coefficient-ring maps between unbounded pro-etale module categories are not a specialization of those hypotheses.

lem-fix-open-scalar-exchange vs sbc-prop-extension-by-zero-and-arbitrary-base-change: gives etale open base change at fixed coefficients, with no scalar-extension or etale/pro-etale comparison square.

lem-fix-open-scalar-exchange vs lem-trf-open-square-exchange: gives fixed-coefficient pro-etale open exchange and geometric pasting, not its compatibility across coefficient categories or across sites.

lem-fix-open-scalar-exchange vs lem-weil-pbc-affine-free-etale-module-eventual-hom-lift: concerns descending maps from finite free etale module sheaves along inverse systems of schemes, not compatibility of open exchange transformations.

lem-fix-open-scalar-exchange vs def-weil-pbc-etale-shriek-base-change-map: defines one fixed-coefficient underived etale mate, rather than asserting compatibility of two such maps with scalar extension or site comparison.

lem-fix-open-scalar-exchange vs lem-weil-pbc-etale-shriek-base-change-modules: proves invertibility of a fixed-coefficient underived etale open mate, not a commuting comparison square.

lem-fix-open-scalar-exchange vs lem-weil-pbc-modulecat-upperstar-free-yoneda: identifies the inverse image of a free etale module sheaf; it has neither derived scalar extension nor site-comparison exchanges.

lem-fix-open-scalar-exchange vs lem-weil-pbc-underived-exchange-module-linear: asserts linearity of the underived etale direct-image exchange at one ring, not the new open comparison equality.

lem-fix-open-scalar-exchange vs lem-weil-pbc-inverse-image-free-etale-module: identifies inverse images of free module sheaves and their generating sections; it does not compare open base-change maps across rings or sites.

lem-fix-open-scalar-exchange vs lem-cbc-derived-extension-zero-base-change-open-pasting: compares composition of open immersions at fixed coefficients on the etale site; it does not involve scalar extension or site comparison.

lem-fix-open-scalar-exchange vs lem-cbc-derived-extension-zero-base-change-underived-compatibility: normalizes the inverse etale open exchange by its unit; the new node additionally compares two exchanges with scalar extension or site comparison on their derived domains.

lem-fix-open-scalar-exchange vs lem-cbc-derived-extension-zero-base-change-vertical-pasting: compares two consecutive scheme base changes at fixed etale coefficients, not a coefficient-ring or etale/pro-etale comparison face.

lem-fix-open-scalar-exchange vs lem-cbc-base-change-mate-stalk: computes geometric stalks of an underived etale open mate; it does not give an equality in the pro-etale derived category across rings or sites.

lem-fix-site-open-exchange vs sbc-prop-extension-by-zero-and-arbitrary-base-change: gives etale open base change at fixed coefficients, with no scalar-extension or etale/pro-etale comparison square.

lem-fix-site-open-exchange vs lem-trf-open-square-exchange: gives fixed-coefficient pro-etale open exchange and geometric pasting, not its compatibility across coefficient categories or across sites.

lem-fix-site-open-exchange vs lem-weil-pbc-affine-free-etale-module-eventual-hom-lift: concerns descending maps from finite free etale module sheaves along inverse systems of schemes, not compatibility of open exchange transformations.

lem-fix-site-open-exchange vs def-weil-pbc-etale-shriek-base-change-map: defines one fixed-coefficient underived etale mate, rather than asserting compatibility of two such maps with scalar extension or site comparison.

lem-fix-site-open-exchange vs lem-weil-pbc-etale-shriek-base-change-modules: proves invertibility of a fixed-coefficient underived etale open mate, not a commuting comparison square.

lem-fix-site-open-exchange vs lem-weil-pbc-modulecat-upperstar-free-yoneda: identifies the inverse image of a free etale module sheaf; it has neither derived scalar extension nor site-comparison exchanges.

lem-fix-site-open-exchange vs lem-weil-pbc-underived-exchange-module-linear: asserts linearity of the underived etale direct-image exchange at one ring, not the new open comparison equality.

lem-fix-site-open-exchange vs lem-weil-pbc-inverse-image-free-etale-module: identifies inverse images of free module sheaves and their generating sections; it does not compare open base-change maps across rings or sites.

lem-fix-site-open-exchange vs lem-cbc-derived-extension-zero-base-change-open-pasting: compares composition of open immersions at fixed coefficients on the etale site; it does not involve scalar extension or site comparison.

lem-fix-site-open-exchange vs lem-cbc-derived-extension-zero-base-change-underived-compatibility: normalizes the inverse etale open exchange by its unit; the new node additionally compares two exchanges with scalar extension or site comparison on their derived domains.

lem-fix-site-open-exchange vs lem-cbc-derived-extension-zero-base-change-vertical-pasting: compares two consecutive scheme base changes at fixed etale coefficients, not a coefficient-ring or etale/pro-etale comparison face.

lem-fix-site-open-exchange vs lem-cbc-base-change-mate-stalk: computes geometric stalks of an underived etale open mate; it does not give an equality in the pro-etale derived category across rings or sites.

lem-fix-open-scalar-exchange vs lem-cbc-finite-open-exchange-scalars: the existing node compares exact restriction of scalars on complexes of B-module sheaves; the new node concerns left derived extension of scalars on arbitrary A-complexes, including non-flat quotients.

lem-fix-site-open-exchange vs lem-cbc-proetale-extension-zero-comparison: the existing node states the individual site-comparison isomorphism and compatibility with composing open immersions; the new node states its normalized equality with geometric open base change.

lem-fix-open-scalar-exchange vs lem-asd-etale-compact-support-normalization: the existing node identifies compactified etale support with etale sum-extension for separated finite-type etale maps between Noetherian schemes, at one fixed coefficient ring; the new node compares derived extension of scalars across two rings with pro-etale open base change, without Noetherian hypotheses.

lem-fix-site-open-exchange vs lem-asd-etale-compact-support-normalization: the existing node compares compactified support and sum-extension within the etale site at fixed coefficients; the new node compares the normalized open base-change maps between etale and pro-etale sites and does not involve a compactification-to-sum comparison.

## Review by Q130

I read delivery-errors B through E, the three blueprint levels in SETUP, GOAL, dag-sync, the returned item and report, and the current item source. I opened every dependency cited by the item and copied the exact clauses used by each step into `citations.json`; each quote is a verbatim part of that node's statement. I checked that every `uses` id exists, is unmerged, and that `proof_deps` is exactly their union. The item statement and its Lean record were not changed.

For the item I read `more-etale.tex` Tags 0GL5 and 0GL6, `etale-cohomology.tex` Tag 0F0G, and `sites-cohomology.tex` Tags 07A6, 07A7, 0E46, 0E47, 0E48, together with the cited DAG statements. Steps 1–7 retain their earlier arguments: K-flat change of rings and ringed-topos adjunctions; etale-origin and boundedness transport; the mate definition and proper qcqs check; the finite-ring proper projection formula; the unit-normalized open beta; and successive-reduction associativity. I rechecked each cited statement against the source node and the hypotheses (finite rings, finite Tor interval, compactification, and arbitrary further quotient).

The returned step is now steps 8–13. Step 8 defines the ambient proper/open compact-support exchange for arbitrary pullback base maps and uses the ambient exchange and pro-etale open base-change statements. Step 9 cites `lem-fix-direct-image-scalar-exchange`, whose statement exactly supplies the coefficient/direct-image exchange equality for arbitrary ring maps and arbitrary complexes. Step 10 cites `lem-fix-open-scalar-exchange`, whose statement exactly supplies the scalar-extension/open-base-change equality with the beta unit normalization. Step 11 is only functorial composition and is marked elementary. Step 12 cites `lem-weil-pbc-transport-identifies-exchange` and `lem-fix-site-open-exchange` to transport the proper and open maps between etale and pro-etale sites, then applies the finite-level pro-etale theorem on the bounded etale-origin witnesses from step 2. Step 13 retains the direct counit/tensor coherence calculation and cites the ringed exchange-tensor coherence and projection definitions. Every formerly inline non-elementary comparison in the returned step is now a named node or an existing cited statement.

I read the source and full statements for each new node. The direct-image node is sourced to sites-cohomology Tag 0E47 and states the mate-pasting cube in the exact coefficient categories. The open scalar node is sourced to etale-cohomology Tag 03S6 and states the beta/open-base-change square with its explicit unit adjunct. The site-open node is sourced to the same open-base-change proof and states the etale/pro-etale comparison equality with both composites and their domains. Each new node introduces its own rings, schemes, sites, functors, and maps; none relies on an undeclared object.

I checked edge cases m=n, the zero complex, empty source, identity, proper, and open-immersion maps, and a non-flat quotient such as Z/ell^2 to Z/ell. The formulas reduce to the scalar/unit identities in those cases, and no finite projective resolution or flatness of B over A is assumed. No statement dispute or hollow definition was found.

### Resumed repair and dry-run findings

The resumed dry run exited with a duplicate-check failure before constructing a delivery. I opened every same-tag node it listed and replaced the generic duplicate paragraphs by the explicit pairwise comparisons above. I also checked `lem-cbc-finite-open-exchange-scalars`: its exact restriction-of-scalars identity is useful background but does not assert the derived extension-of-scalars square in the new node. `fix-lem-exchanges` includes compact-support coefficient compatibility only on the domains of this item's comparison, so using that general coherence clause here would be circular rather than a replacement split.

The three extracted nodes are agent elaborations of the indicated Stacks constructions, not claims that Stacks explicitly states their pro-etale equalities. Tag 0E47 supplies the mate-pasting route for the direct-image cube; Tag 03S6 supplies comparison of right adjoints for open base change. For the scalar node I checked that both displayed composites start at g_B^{-1} S_X j_!^A K and end at j'_!^B S_{U'} h_A^{-1} K. For the site node the endpoints are g_proet^{-1} N_X j_!^et K and j'_!^proet N_{U'} h_et^{-1} K. In both cases the inverse, rather than the forward open exchange, is the unit adjunct. The direct-image cube likewise has common target Rf'_*^B S_{X'} h_A^{-1} M; neither its statement nor the application requires that chi itself be invertible. Identity squares and A=B reduce to naturality/unit identities, while the zero complex and empty open give the zero maps. These tests do not assert flatness for a non-flat quotient.

I compared all 13 steps with the preserved returned proof: steps 1–7 and the final counit step are verbatim, and only old step 8 was replaced. The replacement uses three new smaller statements, the existing proper site-transport theorem, and elementary concatenation. Every non-elementary proof step is below 2000 characters (the largest retained step has 1963). The new statement-only nodes have no proof or proof dependencies. The item statement and Lean record remain exactly equal to the current repository and the preserved returned node. The retained search records match searches.jsonl, including unavailable LeanSearch responses; no search was invented or relabeled as a successful absence result.

The second dry run reached server preflight and flagged three diagram row breaks immediately followed by letters as doubled TeX commands (B4). I separated those rows with newlines and updated the matching verbatim citation text. This changes only the formatting of the three new statements; the item statement, Lean record, and proof remain unchanged.

### Final delivery retry

The fresh dry run against the current server DAG added `lem-asd-etale-compact-support-normalization` to the same-tag checks for the two open lemmas. I opened its statement: its compactified-support-to-etale-sum isomorphism and fixed-ring base-change equality have neither a coefficient-ring comparison nor an etale/pro-etale site comparison. I added the two explicit pairwise distinctions above; the retained repaired nodes, statement, Lean record, citations, and search logs need no change.
