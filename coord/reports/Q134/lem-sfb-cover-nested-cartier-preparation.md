# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cover-nested-cartier-preparation.json: statement item split in nine steps; no Mathlib match for the combined assertion. All original statement, source, creation and blueprint provenance fields retained.
- citations.json: exact statement quotations for every node used in every proof step.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, nested Cartier, nestedCartier, normalization and boundary blowup terminology did not find a declaration giving the full statement. The existing finite-normalization theorem in WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean is an ingredient only. Its normalizationIn construction and finiteness theorem were read, as were Mathlib's normalization and normalizationDesc interfaces.

## WANTED

None. The Stacks sources needed for this assembly are present.

## What needed repair

The item had a statement and searches but no proof. Its statement is mathematically sound and is unchanged. In particular S is not assumed normal: a finite etale cover need not itself be the normalization of S in its generic algebra. The proof uses the relative-normalization universal property to obtain a map to H, rather than claiming the restriction is an etale component. The two distinct boundaries are handled by two successive ordinary blowups. The second blowup preserves the first effective Cartier ideal by the total-transform lemma, without any flatness hypothesis.

The item has no imported blueprint ancestor (tools/blueprint_refs.py ancestor returns None). Its inherited provenance records the original parent steps 1--2 within the direct-image alteration/tame-boundary reduction. I read the current main-20261015 direct-image proof (3), the current unit section, and the chapter record. Their coefficient route is unchanged; this item is a geometric preparation below that route. The repository unit record still points to the older sec-six-functors unit while the item is in sec-six-functors-basics; I preserved that metadata and declared off-unit generic tools in split_report.tool_uses.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own items; none was edited or relabelled as finished.

## Searches and duplicate review

Read the item's inherited searches, then ran logged msearch searches for the item with LeanFinder, LeanSearch, Loogle, and grep. The two natural-language phrasings found normalization constructors and universal-property morphisms; none states the two-boundary geometric preparation. Loogle returned no hits for the normalization/IsFinite combination; grep returned only an unrelated tactic comment. The actual queries and outcomes are appended to the original mathlib_searches. The sandbox searches.jsonl is the command's original log.

Searched the entire DAG by normalization/blowup titles, the Stacks tags 035H, 035I, 035K, 035B, 02OS and 0809, and the underlying concepts. Ran blueprint_refs searches for normalization, boundary, nested Cartier, and normalization finite extension. Existing nodes provide every non-elementary ingredient, so none was created. In particular the finite-normalization result, generic-field normalization, Cartier-boundary blowup, total transform, and integral blowup geometry are reused. No prospective new-node/existing-node pairs remain to justify.

## Review by Q134

I read morphisms.tex Tag 02GL (lemma-etale-over-field), 035H (definition-normalization-X-in-Y), 035I (lemma-characterize-normalization), 035K (lemma-normalization-localization), 035L (lemma-normal-normalization), 035B (lemma-ubiquity-nagata), and 0AVK (lemma-nagata-normalization-finite-general). I also read divisors.tex 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), 02ND (lemma-blow-up-integral-scheme), and 0809 (lemma-blow-up-pullback-effective-Cartier), and the current blueprint statement det-nagata-boundary-divisor-cartier. The item is an assembly of these results, not a claim that any one source already states its whole conclusion. No new-node sources require review.

Step 1 uses the actual statement of lem-weil-pbc-etale-fibre-discrete-separable-points: it gives finite separable residue extensions for every point of a fibre, so it applies to the selected generic-fibre point even when H is disconnected. A dense open S contains the generic point of integral T; its generic residue field is the specified K.

Step 2 uses lem-weil-pbc-normalization-in-residue-field-extension for normal integrality and the generic-field identification, lem-fin-normalization-extension-finite for finiteness over a finite-type field base, and lem-weil-pbc-finite-proper for closedness. The first lemma assumes quasi-separatedness and a finite extension of the chosen point's residue field; separated T and step 1 supply them. Surjectivity is the elementary closed-image argument; I did not silently take it from finiteness alone.

Step 3 spells out the diagonal factorization. The cited closed-immersion base-change and composition statements give exactly its two closed-immersion operations; the finite-type composition statement supplies the other assertion. This is marked elementary because it is a direct two-line application to the two diagonals, with the argument shown. It also supplies the same separatedness calculation for the later composites.

Step 4 uses the normalization definition's integral-closure affine charts to recognize its restriction to S; this is the same construction on the smaller open, not a new geometric assertion. The normalization-in-residue-field statement applied to S supplies the qcqs input needed by the universal-property node. The finite-to-integral statement applies to c, and the universal-property statement gives a map from the normalization to the supplied integral target H. All hypotheses are introduced locally; S is separated since its diagonal is a restriction of T's diagonal. No extension from a normal target, no normality of H, and no identification of H with its normalization is used.

Step 5 explicitly checks all qcqs and quasi-compact-open hypotheses used by the complement-ideal node. Finite type over the field gives local Noetherianity through pqf-lem-locnoeth-lft (a field is Noetherian since its only ideals are 0 and the unit ideal); qcqs-over-affine gives quasi-compactness and quasi-separatedness. The Noetherian closed-subset statement and the compact-subsets leaf then make the needed opens quasi-compact. This argument applies first to X and then to X_1 after step 6 has established properness and step 3 finite type and separatedness.

Steps 6 and 7 use the exact same five statements, read individually: the complement-ideal existence statement gives a finite-type quasi-coherent ideal, integral-blowup-projective-geometry gives integrality for a nonzero ideal, blowup-proper gives properness, global-blowup-complement gives the preserved-open isomorphism, and the first assertion of boundary-divisor-cartier gives the effective Cartier ideal with its exact support. The ideals are nonzero because they equal the unit ideal on a nonempty open. The second centre has support outside V_1, so it is also outside the smaller preserved open. I do not use the product-ideal blowup theorem or a normalization of the blowup.

Step 8 uses cartier-total-transform-blowup, whose statement applies to any ordinary blowup and effective Cartier ideal. It needs no flatness assumption. The support equality is checked in a local generator a: after extension it vanishes precisely above V(a), so the previous boundary is neither discarded nor replaced by its strict transform.

Step 9 uses proper-composition and the full preserved-open isomorphism from steps 6--7. Isomorphism of nonempty opens of integral schemes identifies their generic stalks, hence their function fields compatibly with the maps from K. This explicitly proves the birational assertion without a separability assumption or an unproved function-field transport. Composing the preserved-open inverse with the map from step 4 supplies the required factorization. Unit-ideal blowups are identities by the complement-isomorphism statement on the whole scheme.

I tested empty boundary, equal nested opens S=T^circ, S=T, dimension-zero T, disconnected finite etale H, and nonnormal S. In dimension zero both boundary ideals are units; a generic field factor selects one field component. For S=T with nonnormal T the finite normalization can still map to H by the universal property; it need not be an etale cover. In every case the modification is only required to be an isomorphism above q^{-1}S, never above the larger open. Every step is under 2000 characters and no hidden sublemma is extracted as a redundant new node. All node statements cited in the proof were opened and their complete verbatim statements are copied into citations.json. No statement dispute or weakening was necessary.
