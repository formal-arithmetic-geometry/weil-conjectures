# Stage-1 report: lem-weil-pbc-ind-etale-stability

## New nodes

- `lem-weil-pbc-ind-etale-comp` — statement, attached to `RingHom.IndEtale.comp`; Mathlib searches found no matching declaration.
- `lem-weil-pbc-ind-etale-base-change` — statement, attached to `RingHom.IndEtale.isStableUnderBaseChange`; Mathlib searches found no matching declaration.
- `lem-weil-pbc-ind-zariski-to-ind-etale` — statement, attached to `RingHom.IndZariski.indEtale`; Mathlib searches found no matching declaration.

## Attachments

`RingHom.IndEtale.comp` belongs to `lem-weil-pbc-ind-etale-comp`.
`RingHom.IndEtale.isStableUnderBaseChange` belongs to `lem-weil-pbc-ind-etale-base-change`.
`RingHom.IndZariski.indEtale` belongs to `lem-weil-pbc-ind-zariski-to-ind-etale`.

## WANTED:

None.

## Review by NE

I read the imported blueprint node and the source module `WeilConjectures/RingTheory/ProEtale/IndEtale.lean`, including the attached declarations at lines 356–368 and 399–401. The first item step uses the source composition and base-change statements exactly as recorded in the new nodes, and retains the blueprint's filtered-colimit descent argument. The second step uses the definition node for filtered-colimit ind-etale algebras and the ind-Zariski-to-ind-etale attachment while spelling out the flatness/diagonal argument from the blueprint. The third step uses the base-change and ind-Zariski statements for the tensor-factorization argument and checks the coefficient ring is the same A throughout. I ran LeanFinder, Loogle, and Mathlib grep searches for each new node; all were recorded as no-match because these declarations are source-library declarations, not Mathlib declarations. I verified the citation quotes are verbatim node statements and corrected the item's statement dependencies to include every cited node.

## What was wrong or incomplete

The imported proof had no cited nodes for its non-elementary diagonal and flatness arguments. I split the source-library facts into three attached nodes and made every proof step cite its dependencies. The remaining filtered-colimit descent and weak-etale stability arguments are kept as explicit proof text following the blueprint.

## What could not be finished

No Lean was written or compiled, per the isolated stage-1 instructions.

## Second reading by NE

The sections above preserve the first worker's report. Their claimed attachments are no longer part of this delivery: the three clause nodes were removed and their arguments are written in the parent. The repaired delivery has zero new nodes and zero new Mathlib leaves; it uses existing Mathlib leaves and existing split nodes. No Lean was written or compiled.

- Item statement: compared every clause with the imported blueprint statement and Stacks proetale.tex, 096P (lemma-base-change-ind-zariski), 096Q (lemma-composition-ind-zariski), 096S (lemma-ind-ind-zariski), 097J (lemma-base-change-ind-etale), 097K (lemma-composition-ind-etale), 097L (lemma-ind-ind-etale), 097M (lemma-ind-etale-permanence), and 097N (lemma-ind-etale-implies); weak-etale clauses checked against more-algebra.tex, 092H (lemma-base-change-weakly-etale), 092J (lemma-composition-weakly-etale), and definition-weakly-etale. Verdict: true with the existing definitions; statement unchanged. The blueprint uses finite products of principal localizations as its Zariski building blocks; the repaired argument uses precisely those blocks and does not silently replace them by an arbitrary local-isomorphism definition.
- Original step 1: comp and base-change citations did not give ind-Zariski stability or either colimit assertion; C1/C4/D1 failure, replaced by steps 1–5.
- Original step 2: neither definition nor ind-Zariski-to-ind-etale citation gave the diagonal kernel or flatness; C1/C4 failure, replaced by steps 6–7.
- Original step 3: citations did not establish the diagonal base-change square or flat-map stability; C1/E5 failure, replaced by steps 8–9.
- Repaired step 1: checked the factorization lemma and criterion statements against algebra.tex 00QO (lemma-characterize-finite-presentation) and 07C3 (lemma-when-colimit), and finite-product and open-immersion clauses against the existing cited statements. Verdict: both implications are cited; localization presentation and finite-product idempotent relations are elementary, and zero factors and the empty product are included.
- Repaired step 2: checked the etale-base-change node's clause (1) and tensor/colimit universal properties. Verdict: arbitrary base ring is allowed; the finite-product splitting and localization equations are written explicitly.
- Repaired step 3: checked finite-presentation factorization twice, etale-algebra-filtered-colimit-descent (00U2, lemma-etale, clause (9)), and etale base-change/composition node statements. Compared with algebra.tex 0BSI (lemma-composition-colimit-etale), whose two factorization steps are now present. Verdict: P is finitely presented over R at both uses; the descent node gives an algebra, avoiding an unsupported affine-descent inference. This realizes the blueprint's affine finite-data descent without borrowing the proof of the scheme-descent node.
- Repaired step 4: checked element representatives against lem-pc-filtered-colimit-commrings-elementwise and both factorization criterion statements. Compared with proetale.tex 096Q. Verdict: every denominator is lifted at a common stage; localization of a/f^N is localization at fa, and finite products stay finite. There is no unproved invocation of the etale descent node for Zariski blocks.
- Repaired step 5: checked both cited factorization statements and compared with algebra.tex 0BSJ (lemma-colimit-colimit-etale), including its omitted details. Verdict: successive factorizations prove the criterion without requiring compatible chosen presentations; the optional varying-base interpretation is also justified by an explicit universal property.
- Repaired step 6: checked etale-section-idempotent-splitting on the actual E_i-algebra E_i tensor_A E_i and its retraction; source algebra.tex 00U7 (lemma-map-between-etale), 00U8 (lemma-surjective-flat-finitely-presented). Checked the representative/equality node's two clauses. Verdict: all kernel elements vanish at a late stage, and incompatible choices of stage idempotents cause no problem.
- Repaired step 7: checked localization-flat (00HT, lemma-flat-localization), flat-affine equivalence (01U5, lemma-flat-characterize), flatness in def-weil-etale-morphism, and filtered-colimit-flat-modules (05UT, lemma-colimit-flat). Verdict: quotient/localization inverses and the directed principal localization presentation are explicit; the module colimit is identified from the cited eventual-equality description. Neither ind-Zariski flatness nor etale flatness is asserted without a cited justification.
- Repaired step 8: checked it against steps 1–3 and 7 and the blueprint's third paragraph. Verdict: the displayed theta, pushout map, inverse, and balancing identities give a direct tensor universal-property calculation; this is the elementary part, rather than an appeal to a cited node's proof. The second arrow really is base change of the diagonal of B, not C.
- Repaired step 9: checked flat-ring-map-comp (00HC, lemma-composition-flat) and flat-module-base-change (00HI, lemma-flat-base-change) against their statements and more-algebra.tex lemma-composition-weakly-etale and lemma-base-change-weakly-etale. Verdict: first multiplication arrow is a base change through the displayed tensor identification, the second is flat by hypothesis; both base-change flatness conditions are covered.
- Removed new node lem-weil-pbc-ind-etale-comp: read actual source IndEtale.lean lines 356–360; the local proof agrees with the proposition, but the node restates an item clause (D1), has no commutative-ring hypotheses, and falsely uses status split with no proof. Verdict: remove; parent step 3 proves it using existing nodes.
- Removed new node lem-weil-pbc-ind-etale-base-change: read actual source IndEtale.lean lines 363–368; the local proof agrees with the proposition, but the node restates an item clause (D1), leaves base change implicit, and uses status split with no proof. Verdict: remove; parent step 2 proves it using existing nodes.
- Removed new node lem-weil-pbc-ind-zariski-to-ind-etale: read actual source IndEtale.lean lines 398–401 and the definition node. Verdict: elementary from etaleness of principal localizations and finite products; remove and write that implication in step 1 (C2). The source-library definition uses local isomorphisms; its agreement with the blueprint's product-of-localizations definition was not established by the original attachment record.

Changes and reasons:

- Removed all three never-committed new nodes; composition/base change were clause restatements, and ind-Zariski implies ind-etale is an elementary consequence of existing statements.
- Replaced the three incomplete paragraphs with nine steps, retaining the blueprint route. Expanded denominator descent, the kernel argument, and both tensor squares to repair C1/C4/E5. Preserved the item's statement verbatim.
- Replaced proof-lemma entries in stmt_deps by the definition actually needed to state the item. Recomputed proof_deps and every citation quote from the cited node's actual statement.
- Searched all chapters of dag/nodes by statements, tags and keywords, including filtered-colimit/factorization, affine etale descent, flatness and idempotent splitting. Reused the existing nodes rather than duplicating them. No cited node has a dependency path back to the item.
- Independently ran msearch.py LeanFinder with “Filtered colimits of etale algebras compose and commute with tensor product base extension”, Loogle with “Algebra.Etale, Algebra.Etale”, and grep over the actual whole Mathlib tree with “IndEtale|IndZariski|ind_etale|ind_zariski”. LeanFinder/Loogle return finite etale base-change/composition and related declarations; whole-tree grep returns no ind-etale/ind-Zariski declaration. Actual results are in searches.jsonl. The first worker's grep calls used a redundant Mathlib/ subdirectory and were not reliable whole-tree searches.
- Edge cases checked: R=0; B=0; identity field maps; a zero principal localization; empty finite product (zero algebra/empty spectrum); one localization; kernel J=0 (empty idempotent family gives U={1}); and J=S (inverting 0 gives the zero ring). The ring maps, factorization criterion, diagonal localization and flatness statements hold in each case. Filtered indexing is nonempty by definition; no nonzero-ring hypothesis or surjectivity of transition maps is used.
- The only cross-unit citation outside the proper-base-change route is lem-pc-filtered-colimit-commrings-elementwise, an existing Mathlib leaf, used solely as a generic element/equality tool. Other non-leaf citations belong to sk-thm-p1, a unit explicitly cited by sk-thm-properbasechange.
- Dry-run repair: preflight rejected the first worker's non-null blueprint.from on this imported node (B9). Reset it to null, retaining the proof-place correspondence in split_report.blueprint. The subsequent deliver.py --no-push printed OK; citation, route and DAG checks passed with zero new nodes.
