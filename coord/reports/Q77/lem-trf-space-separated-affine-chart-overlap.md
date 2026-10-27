# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-space-separated-affine-chart-overlap.json`: statement, split; no exact Mathlib match. Five proof steps, 1916 characters total, no step over 2000 characters. Statement retained verbatim; added the existing scheme quasi-compactness and separatedness definition dependencies.
- `citations.json`: ten verbatim quotations, one for each node cited in each step.
- `searches.jsonl`: actual search-command results; inherited searches in the live item retained, today's five searches appended to the item.
- `report.md`: this report and signed self-review.

## New nodes

None. All mathematical inputs already have DAG nodes. Three existing Mathlib leaves supply affine-scheme and affine-morphism facts; the existing closed-immersion definition also includes the affine quotient characterization.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and the notions affine overlap, separated algebraic space and AlgebraicSpace; no project theorem states the item. The scheme-level declarations returned by the search command cannot attach an algebraic-space statement. A read-only search in `lean/Sheaf/` found no item-tagged declaration either.

## WANTED

None. All sources needed for this split are present under `literature/stacks-project/`.

## Findings and corrections

The item's statement is correct as written. Its previous proof was empty. Tag 03M9 is not itself the statement of this item: its proof treats one surjective affine atlas and a quasi-separated diagonal. Here the hypotheses explicitly give a separated diagonal, so its test is closed, and the same compatible-pair computation applies to two independent charts. I wrote the computation rather than asserting the mixed-chart variant. No atlas surjectivity or quasi-compactness of X is needed. The original source field calls 03KM the diagonal definition; the exact definition is Tag 03HL (`definition-separated`), while 03KM is the étale-local criterion. The proof source now distinguishes these tags correctly; the mathematical statement is unchanged.

The live chapter and unit records were read, as were the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md`, `lem-trf-local-term-locality.md` and its proof. The latest unit differs from the archival unit record in its presentation, but neither states this affine-overlap input. The inherited ancestor chain explains the use through the section-algebra/ample-descent input, and the split_report identifies this precisely rather than claiming an affine-overlap sentence exists in the ancestor's proof. The key unit node is not this item; no unit file was edited. The inherited reference to `coord/dag-sync.md` points to an absent file; the explicit live-repository brief supplies the applicable synchronization rule.

## Mathlib and duplicate searches

Ran the required msearch command with LeanFinder twice, Loogle once, grep once, and LeanSearch once. All five services/calls returned successfully. Read the returned hits: `Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine` in Mathlib/AlgebraicGeometry/Pullbacks.lean:489-496, the closed-immersion-to-affine instance in Morphisms/ClosedImmersion.lean:151-152, and `IsSeparated.of_isAffineHom` in Morphisms/Separated.lean:119 onward are scheme results, not the entire item. The second natural-language phrasing returned the same kind of scheme-level facts. No item leaf was claimed. No invented or unrun searches were added.

Searched the entire DAG by affine, closed-immersion, fibre-product and separation notions, and the blueprint index with `blueprint_refs.py search` for affine, closed immersion, affine overlaps, and separated algebraic space. The exact-phrase searches found no blueprint equivalent; broad hits were inspected for reuse. This found the existing fibre-product-of-spectra leaf, affine-local criterion and affine permanence leaf, so none was duplicated. No new id or tag pair exists that requires a not-duplicate justification.

## Not duplicates

No new nodes.

## Review by Q77

I checked the item against spaces-morphisms.tex Tag 03M9 (`lemma-pushforward`), specifically its affine-target paragraph and map R to U times_Y U; Tag 03HL (`definition-separated`) supplies the stronger closed-diagonal assumption actually given here. Tag 03KM (`lemma-separated-local`) was also read to distinguish the definition from its local criterion. The mixed-chart universal-property argument is written in full in step 2. I checked its direction and its compatibility with the projection: removing x and adjoining x=u_0(p_0) are inverse natural maps, and neither changes the pair in P.

Step 1 uses the statement of `lem-trf-presheaf-pullback-etale-point-lifting`, not merely a covering theorem. Its first conclusion says every representable étale singleton remains representable étale under arbitrary pullback; joint surjectivity occurs only in its additional clause. Thus it applies when a chart misses all of X. Swapping the charts gives the other projection. `lem-trf-space-fibre-products-etale-covers` explicitly identifies the sheaf fibre product with the categorical algebraic-space fibre product. I opened both node statements. The source is spaces-topologies.tex Tag 041F (`lemma-etale`), part (3), and spaces.tex Tag 02X2 (`lemma-fibre-product-spaces`), as recorded in those nodes.

Step 2 uses only the explicitly stated fibre-product universal properties in `def-pc-fibre-product` and `lem-trf-space-fibre-products-etale-covers`. Each section triple satisfies u_0(p_0)=x=u_1(p_1), so forgetting x lands in R; conversely the equality in R implies a_0(p_0)=a_1(p_1), hence gives a point of P. This is the elementary compatible-pair calculation, not a new comparison theorem or an uncited use of representability descent. Step 3 uses exactly the definition clause of `lem-trf-space-qc-separated-etale-local`: every scheme test of the relative diagonal is a closed immersion. The test scheme P exists without affineness, so step 3 does not depend circularly on step 4. No closed-immersion base-change theorem is needed in addition to this scheme-test hypothesis.

Step 4 uses the full statement of `def-weil-affine-spectrum` that every map between spectra is induced by a unique ring homomorphism, and `lem-weil-pbc-fibre-product-affine-spectra` gives the actual affine tensor-product spectrum, with the right base ring. I read schemes.tex Tags 01I4 (`lemma-fibre-product-affine-schemes`) and 01JQ (`lemma-fibre-product-affines`). The statement of `def-weil-closed-immersion` already includes the affine quotient-ring characterization; I checked morphisms.tex Tag 01QO (`lemma-closed-immersion`), rather than silently using a theorem not in the cited definition. Taking the whole affine P as its affine open proves R affine. This step is marked non-elementary because the two existing affine theorems do real work.

Step 5 uses exactly the cover clause of `pqf-lem-affine-local-target`, whose source is morphisms.tex Tag 01S8 (`lemma-characterize-affine`): the single open V covers V, and its inverse image is the entire source U_i or R. The three maps are therefore affine; clause (3) of `lem-weil-pbc-affine-morphism-permanence` says affine maps are quasi-compact and separated, including the stronger separated conclusion, not just quasi-separatedness. I read morphisms.tex Tag 01S7 (`lemma-affine-separated`). These are Mathlib leaves and generic tools; they replace no step of the chapter's geometric route. The formula for b is the fibre-product compatibility, so no additional scheme-map existence theorem is hidden here.

For B1-B10 and C1-C8, there are no new unsplit nodes, no moved clauses, no new definition, and no duplicate to create. Every proof use has an existing unmerged node and a literal statement quote in citations.json; quotes were checked as substrings. The proof-dependency list is the union of uses. In D1-D5, the main content remains the natural inverse maps and the affine argument in the item, rather than being renamed as a child. For E1-E7, I verified the relative diagonal is X over V, not X over S; both charts and V are absolute affine schemes, and the graph equality is in X. No finite type, normality, nonemptiness, or quasi-compactness of X was introduced. The empty chart gives empty affine R (the zero quotient ring); disjoint chart images give the same result; equal charts give the usual self-relation; X itself may be a non-quasi-compact disjoint union. For X=V=Spec(k) and finite affine étale charts the relation is their ordinary product. If separatedness is omitted, the line with doubled origin and its two A^1 charts gives overlap G_m whose inclusion into the diagonal A^1 in A^1 times A^1 is not closed; thus the closed-diagonal assumption is substantively used at step 3. All non-elementary steps are short (none over 2000 characters), and the only elementary steps are the explicit inverse-map calculation and application of a definition. No SGA source is used.

I corrected an initial source-tag typo to 03HL after checking tags/tags. No statement correction or dispute was necessary, no work is left unresolved, and no repository, launcher or Lean source was written. The required server dry run and delivery are the remaining operational checks.
