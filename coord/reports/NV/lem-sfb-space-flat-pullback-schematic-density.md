# Stage-1 delivery: lem-sfb-space-flat-pullback-schematic-density

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-pullback-schematic-density.json: item split into five steps, reusing existing nodes; not a Mathlib leaf for algebraic spaces.
- citations.json: one verbatim statement quotation for each of the 19 step/node pairs.
- searches.jsonl: five actual item searches made with msearch.py; their results are appended to the item's previous search records.
- report.md: this report. prepare.py is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for the item. A search under lean/WeilConjectures by the exact blueprint id and by schematic-density/flat-pullback terms found no declaration for algebraic spaces. The scheme theorem is already represented by lemma-nagata-dense-flat-pullback; the more general image theorem is also already represented by lem-sfb-scheme-image-flat-base-change. Neither justifies attaching this algebraic-space item.

## Wanted literature

None. The proof is the etale reduction in Stacks Tag 089D, spaces-morphisms.tex, lemma-flat-morphism-scheme-theoretically-dense-open. I read its proof and the referenced density/flatness descriptions, Tags 0833, 0836 and 03MM, and the scheme theorem Tag 081H in morphisms.tex. I also read the base-change and local quasi-compactness statements (03HF and 03KG), the representable composition/base-change statements (02WK and 02WL), and the current blueprint's lemma-nagata-dense-flat-pullback statement. All sources are already present.

## Corrections and route

The imported item is true under exactly its given hypotheses. Its reference to def-weil-open-immersion defined only scheme open immersions. The statement now specifies representable open subspace inclusion and cites def-a1-space-open-subspace. This clarifies the original algebraic-space open immersion rather than changing a hypothesis. I removed the obsolete scheme-only statement dependency and repaired literal doubled TeX backslashes. I retained the other original fields and original search records.

The proof does not invoke density merely from topological density and does not assume reducedness, Noetherianity, quasi-separatedness of X or Y, or quasi-compactness of f or of an atlas. The quasi-separatedness required by the existing scheme density node is proved for the open immersion itself: its diagonal is an isomorphism. The proof does not cite the item being split or any lemma depending on it.

The inherited blueprint chain has null nearest imported ancestor (blueprint_refs.py ancestor confirmed it); I preserved that provenance and its explicit supporting place. I read the current latest blueprint proof of sk-thm-sf-ctf-stability and its direct-image subproof: this remains a tool on the inherited compactification branch, not a replacement of a unit proof step. Whole-blueprint searches for schematically dense, schematic density, density, flat pullback, scheme theoretically, schematic, and etale schematic yielded no equivalent algebraic-space statement. The scheme density result is reused, not duplicated. No unit realization fields change because this is not the unit's key node.

## Mathlib searches

The five msearch.py calls recorded in searches.jsonl all returned successfully. Loogle found IsSchemeTheoreticallyDominant.pullbackFst, pullbackSnd and of_isPullback. I read SchemeTheoreticallyDominant.lean:38 and 95--124: they concern schemes, with quasi-compactness and flatness as separate hypotheses. The grep found the corresponding scheme-only openness and quasi-compactness base-change instances at OpenImmersion.lean:842 and Morphisms/QuasiCompact.lean:165. LeanFinder's first phrasing returned flat scheme base-change and dominance results, while the second phrasing returned unrelated germ-injectivity results. LeanSearch returned scheme restriction/injective section results, including Scheme.Hom.toImage_app_injective. None is the algebraic-space theorem. All relevant scheme tools already have DAG nodes; no new leaf was needed.

## Not duplicates

No new nodes. In particular the scheme-only lemma-nagata-dense-flat-pullback and lem-sfb-scheme-image-flat-base-change were found and reused rather than recreated.

## Review by NV

I checked delivery-errors.md B--E against the actual node files and the sources, not just against their titles. The five proof steps carry the argument of Tag 089D; no clause is moved into a renamed node. Every used statement is quoted verbatim in citations.json. There are no new statement-only nodes to search, type-check or source. Every proof step is shorter than 2000 characters.

Step 1 uses the actual atlas and small-etale structure-sheaf conventions in def-trf-algebraic-space and the scheme-test definition in def-a1-space-open-subspace. Open-chart-tests supplies the etale nature of an open scheme inclusion followed by an etale chart; chartwise-etale-permanence supplies composition. For every affine open W of the scheme atlas Y_0, W is therefore an affine etale chart of Y, so the item's hypothesis gives quasi-compactness of exactly V times_Y W. The scheme quasi-compactness definition in def-weil-finite-type-morphism now applies directly; I did not assume that a quasi-compact source alone makes a morphism quasi-compact. Monomorphy and the identity diagonal give separation and quasi-separation from the closed-immersion definition. These are elementary arguments written in the step.

Step 2 uses the scheme-representability and surjective-etale pullback clauses of space-fibre-products-etale-covers. Since T is a scheme and Y_0 to Y is representable etale, P=T times_Y Y_0 really is a scheme, even when T to Y is not etale. The map P to T is surjective etale. Chartwise-etale-permanence gives P to X etale when T to X is etale. Thus the square fits exactly the universal chart test in def-sfb-space-morphism-properties. That definition itself supplies flatness of P to Y_0; I did not cite a definition as if it proved a separate flat-descent theorem.

Step 3 uses a surjective scheme atlas T to X, so P to X is a surjective etale scheme cover. Scheme quasi-compact base change states exactly that the base change of j_0 is quasi-compact. The local criterion space-qc-separated-etale-local states a conjunction: quasi-compact AND separated. I verified both local hypotheses, using the open-immersion diagonal argument of step 1 for separation, before applying it. The cited criterion consequently proves actual quasi-compactness of j_X, which in particular gives the chart version requested by the item. This is not a use of only half the hypotheses of the local criterion.

Step 4 uses the direct-image restriction node for its actual section formula and structure-sheaf restriction isomorphism. The assumed etale sheaf injection yields an injection on every Zariski open of Y_0, hence a zero kernel ideal by def-nagata-scheme-theoretic-image. The scheme density node applies to j_0 because it is quasi-compact, quasi-separated, has image Y_0, and the map P to Y_0 is flat. The output is image P, not just dense topological image. Scheme base change makes k quasi-compact. The statement of scheme-image-ideal-qc explicitly gives injectivity on sections of the image for a quasi-compact map; since that image is P, it gives exactly the section injection used here. I do not use that node's support clause.

Step 5 tests the desired monomorphism on every etale object T, rather than only asserting it from injectivity on one atlas's global sections. The direct-image section formula identifies the restriction with sections on T times_X (X times_Y V). After pulling back to P, associativity identifies the zero restriction with the restriction used in step 4. Sheaf uniqueness for the surjective etale covering P to T then says s=0. No exactness or base-change theorem for arbitrary sheaf pushforwards is being assumed.

Edge cases: if X is empty all tests and assertions are vacuous; if V is empty, the given sheaf injection forces each atlas's structure sheaf to vanish and hence Y to be empty, so the argument still applies. If V=Y the maps in question are identities. Disconnected atlases and nonreduced or non-Noetherian schemes cause no change: the proof uses injective structure-sheaf maps and scheme-theoretic images, never generic points or reducedness. Non-quasi-compact source atlases are allowed throughout. The family of covers is small in the fixed universe convention.

The off-unit citations are generic atlas, quasi-compactness and structure-sheaf tools; split_report.tool_uses declares them for the maintainer. They supply tools below the inherited compactification route and do not replace any chapter or unit step.

## Unfinished work

None in this one-level split. The existing cited open nodes retain their own queued work; no new obligations are hidden in new nodes.
