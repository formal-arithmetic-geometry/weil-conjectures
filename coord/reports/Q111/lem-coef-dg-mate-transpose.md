# Q111: lem-coef-dg-mate-transpose

## Files written

- dag/nodes/sec-six-functors/lem-coef-dg-mate-transpose.json: existing statement node, now split into five steps; no Mathlib match.
- citations.json: one verbatim statement excerpt per step/node citation.
- searches.jsonl: actual outputs recorded by msearch.py, retained in the sandbox.

No new nodes or Mathlib leaves. No unit record is changed; this item is a foundation below the unit's key nodes.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint tag, the item id, enhanced/enriched adjunction, mateEquiv and transpose. The ordinary base-change mate calculations in SixFunctors/Etale/LowerShriek/OpenImmersion/BaseChange.lean and related modules do not state an equivalence of D(Z)-enriched transformation objects with coherent parameter simplices. No exact project declaration was found. Upstream master is reference material only and the item id is absent there too.

## WANTED

None. This is an agent-written formal argument from the item's explicit enhanced adjunction hypotheses and the existing structural node, not a claimed Stacks theorem or an unarchived external proof.

## What was wrong or incomplete

The item was statement-only, so the equivalence of whole transformation objects and its restriction compatibility needed a proof. The statement is unchanged. In particular, the ordinary mate bijection in def-weil-pbc-adjunction-mate is used only to fix the directions of the word, not to infer enhanced transposition. No SGA route is used.

Read the chapter and unit JSON records. Read both the historical master ancestor prop-coef-integral-exceptional-adjoint (proof paragraph 2: finite units and counits before derived inverse limit) and its current main-20261015 version under sk-thm-sf-package (statement only). The historical ancestry and the maintainer-owned unit binding remain unchanged; this foundation performs no geometric rerouting or coefficient-category identification.

## Mathlib and duplicate searches

The original item's search records are preserved. Ran six additional logged searches with msearch.py: LeanFinder for enriched adjunction mapping objects; Loogle for mateEquiv/counit; a CategoryTheory grep; LeanSearch for coherent parameter transposition; a focused Mates.lean grep; and a second LeanFinder phrasing in terms of inverse unit/counit formulas. All services returned hits. Read Mathlib/CategoryTheory/Adjunction/Mates.lean:84-128 and Enriched/FunctorCategory.lean:16-28,43-91, plus Enriched/Basic.lean:395-440. The mate formula is present for ordinary categories, and the enriched functor file uses ordinary indexing categories and ends. Neither is the full enhanced infinity-categorical assertion. No result is reported as unavailable or as a matching leaf.

Searched the whole DAG for enhanced/enriched adjunctions, enhanced mates, coherent transposes and mapping-object/end formulas. Ran tools/blueprint_refs.py ancestor on the item and whole-blueprint searches for mate, enhanced adjunction and transpose. Read the statements of lem-coef-enriched-category-tensor-calculus, lem-coef-coherent-end-twisted-arrow-formula, lem-coef-enriched-hom-twisted-arrow-comparison, lem-coef-cartesian-section-adjoint-mates and def-coef-coherent-adjunction-data. The first supplies the needed enriched functor operations. The end formula is space-valued and would not alone justify D(Z)-enriched mapping objects; the cartesian-section theorem has additional geometric and coefficient hypotheses. No duplicate node was created.

## Not duplicates

No new nodes: no new/existing pairs require justification.

## Review by Q111

I read the historical source proof paragraph 2 with the item and both cited statements open. The source motivates compatibility of the specified finite units and counits, but does not prove the enhanced categorical foundation. Therefore proof_origin.by is agent. I checked that every enhanced adjunction, unit, counit, naturality homotopy and coherent triangle used in the proof is explicitly part of the item's assumptions. I did not replace those assumptions by an adjunction of ordinary homotopy categories.

Step 1 uses lem-coef-enriched-category-tensor-calculus: its statement gives enhanced internal functor categories, coherent composition/evaluation/currying and the D(Z) specialization. These supply postcomposition on the full mapping objects and composition with the unit/counit points. The displayed T and S are morphisms in D(Z), so generalized inputs need not be degree-zero elements. P=GR1 has target C2 and Q=H has target D2; LP and RQ therefore lie in the claimed functor categories. The universes are explicitly enlarged as the item permits.

Step 2 uses that same coherent composition statement and the given enriched naturality of epsilon. In TS(a), counit naturality changes epsilon_Q LR(a) into a epsilon_LP, and the given left triangle cancels epsilon_LP L(eta_P). This is an elementary two-line calculation on the universal mapping-object input; it does not use the invalid inference that pointwise equality determines a coherent transformation homotopy.

Step 3 uses the same structural statement. Unit naturality changes RL(b) eta_P into eta_RQ b, then the right triangle cancels R(epsilon_Q) eta_RQ. Thus both inverse homotopies are maps of derived objects. Only the explicit triangles already assumed by the item are needed. Steps 2 and 3 contain the argument rather than offloading the equivalence to a new node.

Step 4 uses def-weil-pbc-adjunction-mate only for its written order and the component domains, and the enriched calculus for coherent functoriality. I checked c has source L2 G R1 and target H, that R2(c) eta2_P is exactly the three factors of beta, and that applying step 2 supplies the specified enhanced comparison. No assertion about invertibility of alpha or beta is needed; alpha is arbitrary.

Step 5 uses the cotensor identity and coherent composition/evaluation in the calculus statement. I wrote how restriction acts on T, S, the naturality homotopies, both triangles and the beta=S(c) comparison, not merely that coherence is standard. Parameter shapes and their restrictions are allowed by the cited statement, including simplicial shapes. Thus faces and degeneracies are restrictions of the same data, not new componentwise choices of homotopies. The citation excerpts in citations.json occur verbatim in the relevant statements.

For small cases I checked identity adjunctions (T and S become the identity and beta=c), zero transformations in D(Z) (both formulas preserve zero), empty parameter/source diagrams (the same operations and identities exist on the unique empty diagrams), and a noninvertible alpha (the proof never assumes its inverse). There are no new statements to audit for missing hypotheses. I reviewed delivery-errors B through E: no new node, no hidden non-elementary end/limit theorem, no source tag falsely attributed, no clause relabeling, and no ordinary/enhanced ambiguity. Every step is below 2000 characters; steps 2 and 3 are the explicit triangle calculations, not hidden comparison lemmas. No previous completed files or delivery were present when resuming; existing source metadata and all earlier search records were retained.

## Unfinished work

None in the stage-1 split. The cited structural node remains an existing foundation in the DAG; it is not claimed to be proved by this delivery. No Lean was written or compiled and no live project file was changed.
