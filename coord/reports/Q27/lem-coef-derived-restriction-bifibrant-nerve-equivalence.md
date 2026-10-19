## Worker report

Item: lem-coef-derived-restriction-bifibrant-nerve-equivalence. Group: Q27. Stage 1 only, direct delivery. The sandbox initially contained dispatcher markers only, so the item was copied from the shared DAG; no earlier split or report was overwritten.

### Files written

- dag/nodes/sec-six-functors/lem-coef-derived-restriction-bifibrant-nerve-equivalence.json: statement, split into eight proof steps; no Mathlib match.
- citations.json: a verbatim statement excerpt for each of the sixteen step/node citations.
- report.md: this report and review. searches.jsonl is the search command's unaltered log. write_split.py is sandbox-only working material.

New nodes: 0. New Mathlib leaves: 0. The item's statement and its four statement dependencies are unchanged. No Lean was written, compiled, or attached. No shared or live project file was edited and no git command was run in the shared repository.

### Sources and route

I read the chapter record sec-six-functors and unit sk-prop-sf-biduality-general, SETUP's three levels, GOAL.md and coord/dag-sync.md. This is a generic foundation supporting the existing coefficient-adjunction argument, not a replacement for a unit step. The blueprint ancestor is prop-coef-integral-exceptional-adjoint; I read paragraph 2 of its main-20261015 proof, introducing derived coefficient adjunction immediately before the displayed derived Hom/limit calculation. Its text does not prove the present enriched replacement assertion, so proof_origin is explicitly agent. The existing precise ancestry through the rectification node and its returned step 7 is preserved.

I read Lurie, Higher Algebra, Theorem 1.3.4.20, Lemma 1.3.4.21 with its proof, and Remark 1.3.4.27 online at https://www.math.ias.edu/~lurie/papers/HA.pdf (printed pp.117-118,120). Lemma 1.3.4.21 constructs a replacement/right-adjoint composite and proves the equivalence by weak replacement unit maps. I expanded this route using the existing coherent derived-adjunction theorem, then proved the comparison for the *given* enriched Q using the canonical ordinary-nerve square and the entire localization universal property. The source.document was corrected from HTT to HA: the former node cited theorem numbers belonging to HA. There is no statement correction or dispute. No Stacks tag states the enriched comparison theorem; no SGA reference is used.

WANTED: Lurie, Higher Algebra, archived in literature/, Theorem 1.3.4.20, Lemma 1.3.4.21 and Remark 1.3.4.27, for lem-coef-derived-restriction-bifibrant-nerve-equivalence. Online reading is recorded; I did not download or edit literature.

### Attachment and reuse searches

I searched WeilConjectures/ of /home/ubuntu/weil-src-slopmaster2 for the exact item id, Quillen equivalence/QuillenEquivalence, coherent nerve and bifibrant. No project declaration states the item. The upstream-name index gives no item attachment. Master sorry declarations were not treated as proofs.

I searched the whole DAG by Quillen equivalence, coherent nerve, enriched natural transformation, unit/counit equivalence and homotopy-category equivalence. I read the existing enriched-right-Quillen-equivalence node: it assumes every target object cofibrant, so it cannot be applied here. Its checked ordinary-bifibrant nerve comparison is useful precedent, but none of its proof is silently used as a cited theorem. I also read the narrower enriched-evaluation-replacement-coherence and simplicial-natural-equivalence-homotopy statements; neither is substituted for a full localized functor comparison.

blueprint_refs.py ancestor identifies the preserved ancestor above. Whole-blueprint searches for Quillen equivalence, bifibrant, and cofibrant replacement found no matching imported statement, so blueprint.same_as remains []. No node was created.

The item's seven inherited Mathlib search records were retained. Six additional searches were actually run using msearch.py, recorded unchanged in searches.jsonl and appended to mathlib_searches with their exact tool and query. LeanFinder was tried with two different phrasings, plus LeanSearch, Loogle and two source greps. Returned hits concern ordinary nerves/truncations, ordinary derived adjunctions and ordinary localizations. I read Mathlib/AlgebraicTopology/SimplicialNerve.lean:14-34, ModelCategory/CofibrantObjectHomotopy.lean:131-178, and CategoryTheory/Functor/Derived/Adjunction.lean:37-58,144-150. The coherent nerve file lists its locally-Kan quasicategory theorem as future work; resolutionObj/resolutionMap do not give the specified enriched replacement functor (the latter is only functorial up to homotopy); derived' and derived assume ordinary Category instances. The other grep hit is SingularSet.lean:37's future-work comment. None proves this item or a one-line generalization. All six new searches completed; no service failure was described as absence.

### Tool use and unchanged dependencies

lem-cbc-enhanced-functor-cone-calculus is an off-unit generic tool for the componentwise equivalence criterion. Its use is declared in split_report.tool_uses for maintainer acceptance, without setting the maintainer-owned tool_uses field. The statement of that node explicitly supplies the criterion missing from the model-localization and derived-adjunction statements. All other proof nodes are in this item's unit. I checked that none of the five cited nodes depends transitively on the item. A transient malformed unrelated shared JSON file, lem-coef-terminal-local-kan-corepresentability, was observed during a local read; I did not edit it and rely on the required server validation for the delivered overlay.

Nothing mathematical is deferred within this item's proof. Its existing prerequisites remain independent DAG obligations. No new lemma, proof sketch inside a statement-only node, hidden assumption of R preserving cofibrants, or new axiom is introduced.

## Not duplicates

No new nodes, hence no new/existing pairs requiring separation. In particular lem-coef-enriched-right-quillen-equivalence has the stronger all-objects-cofibrant hypothesis and is not used to prove the general case by specialization.

## Review by Q27

I reread the item, all five cited statement files, HA's replacement proof, and the coefficient-adjunction blueprint paragraph with delivery-errors B through E open. I retained the statement exactly: combinatorial simplicial model categories, a simplicial Quillen equivalence, arbitrary supplied enriched Q with enriched natural trivial-fibration q, and enlarged universes. Enriched Q is an assumption, not something claimed to exist by combinatoriality. There is no uniqueness requirement on Q.

Step 1 uses the preservation clauses of lem-coef-model-infinity-derived-adjunction, not merely the definition of Quillen adjunction. The source of QRY is cofibrant by assumption; its fibrancy follows by composing q_RY with the terminal fibration of RY. The simplicial model axiom is explicitly present in lem-coef-simplicial-model-nerve-localization and proves local Kan mapping sets. Two-out-of-three proves Q preserves weak equivalences, so no unprovided Brown lemma about Q is assumed.

Step 2 uses the actual replacement unit formula in the model-infinity-derived-adjunction statement. The criterion is applied with cofibrant P=QX and fibrant TLP, to t_LP; these are precisely the hypotheses it requires. The elementary argument produces a weak adjunct and inverts q_X in localization.

Step 3 uses that same node's actual counit formula. I explicitly checked that the adjoint of epsilon_Y composed with Lq_RY is q_RY, including its direction. The input QRY is cofibrant even when RY is not. Fibrant replacement supplies representatives for every localized object. The cited enhanced-functor-cone-calculus statement says verbatim that a transformation is an equivalence iff all vertex components are equivalences; thus the argument reaches whole coherent unit/counit transformations, not just a homotopy-category adjunction.

Step 4 uses both clauses of model-nerve-localization: the bifibrant nerve comparison agreeing with inclusion, and equivalence of the ordinary bifibrant localization with the ambient localization. It explicitly invokes that node's entire functor-category universal property. coherent-nerve-comparison supplies the ordinary/discrete-nerve identification. This makes j a localization and its restriction fully faithful; no claim that merely identical object functions determine coherent functors is made.

Step 5 checks the strict ordinary-nerve square simplex by simplex using preservation of the given enriched composition. The qR comparison is a natural transformation on the ordinary bifibrant category with weak components, so its localized nerve is a coherent equivalence by the cited componentwise criterion. model-infinity-derived-adjunction identifies the derived right functor there, since R sends the weak fibrant-replacement comparison between fibrants to a weak equivalence. In particular the comparison is natural on arrows and higher simplices.

Step 6 lifts the equivalence, its inverse, and inverse homotopies through the fully faithful restriction from step 4. This is a short consequence of the cited full localization property, so I kept it as an elementary step rather than creating a node restating this item. The displayed inverse e_N^{-1} LL e_M has the correct direction. Step 7 uses the actual natural and composition-compatible mapping comparison of coherent-nerve-comparison together with model-nerve-localization. These statements explicitly give all mapping spaces and composition homotopies, so nothing is taken only from a cited node's proof. Step 8 expands the Joyal testing definition: whisker the two inverse equivalences to obtain inverse restriction functors, then pass to ordinary homotopy categories. The quoted Joyal statement is exactly this convention.

Small-case checks: with the identity Quillen pair and Q=id the proof reduces to identity functors; with the identity pair and nonidentity Q it uses q to identify the resulting nerve functor with identity. When RY is fibrant but not cofibrant, step 3 still uses QRY, so the key excluded false inference never occurs. The argument does not require nonempty mapping spaces; empty Kan mapping sets and disconnected components are allowed. The terminal model category gives point nerves and trivial inverse transformations. Universe enlargement precedes all ordinary and coherent nerves. Replacing Q by a different supplied enriched replacement repeats the same comparison, so no unasserted functorial enriched replacement construction is needed.

I corrected the documentary HA/HTT mismatch and expanded the ordinary-bifibrant localization square that an objectwise-only argument would miss. No statement weakening was needed. Every non-elementary inference is a stated clause of an existing node with a verbatim citation. The eight step lengths are 973, 774, 892, 1226, 1073, 757, 845 and 826 characters; none exceeds the human's 2000-character review threshold. There are no new nodes to audit for B1-B9 or elementary/duplicate/clause relabelling. This is my direct-delivery review; the maintainer independently reviews the mathematics.
