# Q121 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-etale-source-target-properties.json`: item, statement; split into nine steps, no exact whole-item Mathlib match.
- `citations.json`: one verbatim statement quotation for each cited node in each step.
- `searches.jsonl`: search-command log; preserved, with every recorded query also appended to the item's existing Mathlib search history.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. All prerequisites already exist. The earlier candidate new nodes (smooth base change and open-source locality) were rejected as duplicates before creation.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact item id and blueprint docstring tag and by the source/target locality notions. No project declaration states the whole item with an unsorried proof. Individual permanence declarations and Mathlib facts are not an attachment of this item.

## WANTED

None. All sources used are present locally. No downloads, Lean edits, compiles, Lake commands, repository writes or repository git commands were performed.

## Issues found and changes made

The imported statement is consistent with Stacks Tags 04QZ, 04R1 and 04R3, including the pointwise chart criterion and arbitrary jointly surjective etale source families. It is unchanged, as are its statement dependencies. Its proof was empty. I supplied the argument without creating clauses of the item as artificial new nodes.

The inherited blueprint ancestor is null and the inherited `from.place` is already specific. I retained its full provenance/via chain. I read the latest blueprint `main-20261023-1620` direct-image stability proof (3); its current paragraph uses compactifications, while the inherited node records the older alteration prerequisite chain. Whole-blueprint searches for etale locality, fpqc/source descent, composition, finite presentation, smoothness, flatness and the permanence tags found no equivalent imported node. `same_as` remains empty; I have not invented a blueprint ancestor.

No statement dispute, hollow definition or new unproved object is introduced. External non-Mathlib tool uses are declared in `split_report.tool_uses` rather than replacing a unit's proof route. These are the existing generic smooth-base-change and source-descent/algebra statements.

## Unfinished work

None in the mathematical split. Delivery validation and pushing are performed after this report is written.

## Not duplicates

No new nodes. Existing nodes are reused for smooth base change (`lem-pc-proper-base-change`, clause (2)), smooth/etale Zariski source locality, every composition and base-change property, and single-source descent. No same-tag pair of a new and existing node arises.

## Review by Q121

I read `coord/delivery-errors.md` B–E in full and reviewed this split against its mathematical failure cases. For the item I read Stacks `descent.tex` around Tags 04QZ, 04R1 and 04R3 in full, including the characterization's implications and the listed five properties. I also read the source-descent sections for flatness, local finite presentation, local finite type, smoothness and etaleness (in particular Tags 036N, 036U and 036W), and the corresponding composition/base-change paragraphs in `morphisms.tex` (01T3/01T4, 01TR/01TS, 01U7/01U9, 01VA/01VB, 02GW). There are no new-node sources to audit.

For step 1 I opened and read the etale, smooth, unramified and open-immersion definitions. The etale definition supplies flatness and local finite presentation; its unramified clause, together with the unramified definition, supplies local finite type directly. The smooth definition explicitly says etale maps are smooth of dimension zero. The etale permanence statement, clause (1), supplies open immersion implies etale. An identity is an open immersion by the definition, including on the empty scheme. This avoids hiding the more general affine-local finite-presentation-to-finite-type theorem as an elementary inference.

For step 2 I checked the full statements of smooth composition, etale composition/cancellation, lfp composition, proper/fp permanence and flat-ring-map composition. They all concern arbitrary schemes or rings. The proper/fp node is used only in its explicit clause (e), not its properness or global finite-presentation clauses. The flat morphism definition identifies exactly the two stalk maps and their composite; flat-ring composition proves the needed flatness. Thus composition with an etale map works on both sides for all five P, not just precomposition.

For step 3 I checked the full proper/smooth base-change statement and selected clause (2); etale-base-change/finite-limits clause (1); flat base change; qcqs permanence clause (3); and lft base change. Each explicitly allows an arbitrary base-changing morphism. I did not infer arbitrary base change from a theorem restricted to etale base changes, nor import the qcqs hypotheses from the other clauses of the qcqs node. These facts are already in the DAG, so no new base-change node is warranted.

For step 4 I checked the four source-descent statements. Smoothness allows a jointly surjective etale family, so a singleton applies. Etale descent requires exactly surjective and etale. Lfp source locality requires flat and lfp, both supplied by step 1. Lft source descent requires the same plus surjectivity. None requires q quasi-compact or any scheme Noetherian or separated. These are source descent statements, not fpqc target-base-change descent misapplied on the source.

For step 5 I read the etale-stalk-invariants statement and use only its explicitly stated faithful flatness, not any assertion of equality of residue fields or any dimension comparison. The flat permanence statement is about R→S and an S-module M flat over R and faithfully flat over S. With R=A, S=B and M=C its two hypotheses follow respectively from the flatness of fq and the etale stalk map of q. This proves flatness of A→B at the chosen x. Only surjectivity is used to choose u; no global faithful-flatness or quasi-compactness theorem is being assumed. The empty X case is vacuous.

For step 6 I checked the coproduct node's complete statement: set-indexed coproducts, open coprojections, pairwise disjoint components covering the coproduct, and its universal property. The etale and smooth source-locality statements apply to these open components. For flatness the cofinal-neighbourhood argument identifies component stalks. The lfp definition is pointwise, so its affine neighbourhood remains open in the disjoint union; the lft definition is checked separately on each affine target open by union of the given affine covers. These are direct applications of definitions, not an uncited general locality theorem. No bound on I or quasi-compactness is inserted. The empty open cover is allowed by the smooth statement and by the general cover formulation of the etale statement; flat/lfp are vacuous, and lft uses an empty affine cover. Thus every P holds for a map with empty source, exactly as the statement requires.

For step 7 I read the fibre-product universal property and etale cancellation clause (3). For B=U×_Y V the projection to U is the base change of b, and the projection to V is the base change of bk. Step 3 therefore applies to the correct respective maps. The graph s is a section of p_U, so p_U s=id_U; cancellation gives s etale from the etaleness of p_U and id_U. No assertion that the graph is closed or that b is separated is used. Composing s with the P-map p_V proves P(k).

Steps 8 and 9 only assemble earlier results. In the square, the direction P(f)⇒P(h) uses cancellation of b, whereas the converse needs surjectivity of a, and this hypothesis is present. In the pointwise criterion, the indexing set is the set of points of X; choosing one given pointed chart for each x yields a jointly surjective family. The empty case is the already verified empty family. Identity charts prove the forward direction. I checked identities, empty sources/targets where maps exist, arbitrary infinite disjoint unions, non-quasi-compact covers and nonseparated etale target maps. There is no false strengthening to a single globally surjective pointed chart.

Every cited node's actual statement was opened, including mixed-clause nodes, and `citations.json` copies verbatim the clause used (or its full statement). I checked the dependency closures of the new citations for cycles back to this item. Whole-DAG and blueprint searches were made before considering new nodes, and all prospective new lemmas were found already present or elementary. The required Mathlib searches used only `msearch.py`; I read the semantic and Loogle hits and the pinned source, and retried with different phrasings. They identify individual permanence/locality facts, not the complete item. The original search history is retained. All nine steps are below 2000 characters; the coproduct and graph steps explicitly give their arguments rather than hiding comparison lemmas. No SGA route, sheaf/coefficient-category substitution or unsupported axiom is involved.
