# Q135 stage-1 delivery

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-etale-cartesian-tower-tensor-comparison.json`: item, statement; split using existing nodes. Statement and statement dependencies preserved. New searches found no Mathlib match.
- `citations.json`: one verbatim statement quote for each of the 15 step/node citations.
- `searches.jsonl`: actual search-command log, preserved.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No Lean files or repository files written; no compiler, Lake or local preflight/check scripts run.

## Attachments

None. I searched the project source under `lean/WeilConjectures/` by the exact blueprint id, etale/dualizing tensor language, and dualizing-composition declaration names. The nearby `nonempty_iso_dualizingComplex_comp_of_isInvertible` and `IsCohomologicallySmooth.nonempty_iso_dualizingComplex_comp` in `EtaleCohomology/Purity/Smooth/CohomologicallySmooth.lean` give existence of isomorphisms, rather than these equalities of specified normalized maps; their ordinary etale statements do not attach this item. I also read the actual tensor-map declarations and coherence source. No exact project declaration was found.

## WANTED

None. The current blueprint source and the existing node statements suffice for this assembly.

## What needed repair

The item was unsplit with no proof. It is not disputed and has no released repair note. Its three conclusions follow by algebraic assembly of the existing etale normalization and general sigma-cocycle statements; no new lemma is required. The proof now spells out the tensor substitutions, the direction of the inverse, and the E comparison for the composite etale map. It does not infer a Cartesian square for F and G.

I retained every original field, including the inherited Mathlib search records, source, creation record, chapter, unit and blueprint ancestry. I appended the searches made during this dispatch. Loogle rejected the two queries using unrecognized conjugateEquiv names; these are recorded as failed queries with no evidence of mathematical absence. The successful `SheafOfModules.pullbackComp` query and the two semantic phrasings provide useful results. All search outputs were read. The module-sheaf pullback and conjugate-comparison hits concern ordinary pullback, not exceptional dualizing tensor comparisons; I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`. The grep query returned no extraordinary or dualizing comparison hits.

## Not duplicates

No new nodes were created. I searched the whole DAG for sigma, etale normalization, tensor composition and cocycle statements, and searched the imported blueprint with `blueprint_refs.py search` for `dualizing tensor`, `dualizing`, and `composition coherence`; I also ran `ancestor` for the item. `lem-pur-finite-etale-dualizing-normalization` supplies precisely the first inverse identity and normalized unit formula; `lem-pur-dualizing-sigma-cocycle-locality` supplies the general three-arrow associativity law and its etale-source specialization. The latter has no proof dependencies currently, but is a legitimate existing unsplit dependency to reuse, not a finished proof claim. Neither existing statement is the whole mixed Cartesian/etale tower item. I did not create duplicates of either one. `lem-pur-smooth-exceptional-tensor-pasting` concerns Cartesian base changes of a whole tower and is unnecessary here.

## Review by Q135

I read the stage-1 brief, the stage document, SETUP's chapter/unit/node restrictions and generic-tool rule, GOAL, the item chapter and unit, and delivery-errors B through E in both sections of that file. I read the current main-20261015 proof of `thm-pur-composition-coherence` in full: Step 1 asks for compatibility with etale localization and the composition pentagon; this proof supplies exactly that constituent without invoking a purity orientation or changing the diagonal/DNC route. I also read the etale-locality proof in the six-functor basics unit. The blueprint source is agent-written, so `proof_origin.by` is `agent`. I read Stacks Morphisms Tags 02GO (`lemma-base-change-etale`) and 02GN (`lemma-composition-etale`) at lines 8136 and 8121 for the geometric prerequisites. No SGA route is used.

For Step 1 I opened the statements of `lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-composition-cancellation`, `lem-sbc-smooth-relative-dimension-permanence`, and `def-pc-fibre-product`. They respectively give J etale as base change of G, F etale as a composite, smoothness and the dimensions of the needed composites (etale dimension zero), and the commutative square. All morphisms are already separated finite type by the item; none of these tools requires the schemes to be absolutely separated. In particular q_Q and a have dimension d_q, and b has dimension d_p, even on empty schemes.

For Step 2 I read clause (3) of `lem-pur-finite-etale-dualizing-normalization` literally: beta is sigma-inverse followed by E-inverse, with the unit eta identification. Its hypotheses have exactly our finite coefficient stage, arbitrary finite-type k-schemes, smooth vertical maps and etale horizontals. Inversion gives the first asserted equality with the correct direction. I did not use an unnormalized existence isomorphism.

For Step 3 I read the first displayed cocycle in `lem-pur-dualizing-sigma-cocycle-locality` and clause (3) of the normalization. Substitute u=q_Q, v=G, w=p. Precomposing the cocycle with the inverse of 1 tensor q_Q^*sigma_{G,p}, and using E_{G,p}sigma_{G,p}=eta_G tensor 1, gives the explicit formula in the step. The surviving map is E_{G,p}, whose source is omega_b, rather than its inverse. This check prevents a type error in the second factor.

For Step 4 the same cocycle statement explicitly gives the etale-source identity for u=J, v=q, w=p. Since Gq_Q=qJ, substitute Step 3 and the already proved Step 2 and compose the two tensor factors. This is a few lines of functoriality and equality substitution, so this step is elementary with its actual general identity cited. There is no hidden base-change compatibility lemma here.

For Step 5 I opened `thm-sf-comp-composition`, `lem-weil-pbc-mate-pasting`, `def-pur-finite-exceptional-composition`, and clause (2) of the normalization. The first says the specified compact-support compositor is associative on finite-type k-schemes without absolute separatedness; the second explicitly states pasting along the composite adjunctions, including the composite counit; the definition identifies c as its conjugate. Thus the displayed c equation is the conjugate of that associativity equation. Clause (2) gives rho_{JH} in terms of rho_H, rho_J and c_{J,H}, and naturality of the natural isomorphism rho_H moves c_{pq,J} past it. Expanding these two equations gives LH^*E_{J,pq} E_{H,pqJ}, exactly the claimed E_{F,pq}, without assuming a new normalization.

For Step 6 I reread the etale-source specialization for u=H, v=q_Q, w=b. It has no Cartesian hypothesis. I opened `lem-weil-pbc-proetale-derived-pullback-composition` and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: their statements give the canonical derived compositor and monoidal comparison, natural in both factors, for arbitrary schemes/ringed topoi. With constant finite coefficients these identify H^*q_Q^* with a^* and H^*J^* with F^* and distribute pullback over the tensor input map. Pullback of Step 4 followed by Step 5 then gives the final formula. I checked both its source and target against the item. No Cartesian use is made after the original square in Steps 1–2.

I checked C1 by listing every non-elementary ingredient in these paragraphs against the `uses` lists. I checked C4 by copying entire verbatim statements into citations.json; in particular the cocycle and etale normalization contain the exact formulas used, not just a definition or a weaker full-faithfulness result. Proof dependencies equal the union of uses. The few off-unit generic tools are declared in split_report.tool_uses; they supply operations/geometric permanence, not another proof route. I traversed the statement/proof dependencies of the proposed citations and found no path back to this item, including from the existing unsplit cocycle. No statement-only nodes were created, so there is no clause relabelling. All six steps are below 600 characters and none hides a long lemma.

I checked small cases: G=id makes J=id and beta=id, so the first formula becomes a unit identity and the second reduces to the identity for sigma_{q,p}. H=id recovers the second formula from the third and E_id is the normalized identity. q=id makes q_Q=id and the Cartesian comparison a unit; the second formula is the etale-source identity for G and p. With p=id the normalized unit rules reduce the second formula to the first tensored with the coefficient unit. Empty schemes give maps in the zero category and the permanence node explicitly permits them. For a genuinely non-Cartesian final square take q=p=G=id on A^1 and H the inclusion of a proper open subset: the final identity is still an etale-source/unit identity and the proof imposes no surjectivity or Cartesian condition on H. No Tate twist or orientation choice occurs in any check.

## Unfinished work

None within this one-level split. Existing unsplit dependencies retain their own proof obligations; this delivery makes no claim to finish them.
