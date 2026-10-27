# Stage 1: lem-sfb-weakly-etale-indetale-cech-refinement

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-weakly-etale-indetale-cech-refinement.json: item split into five steps. Statement and statement dependencies unchanged. No new nodes, no new Mathlib leaves.
- citations.json: exact statement quotations for every cited node in every step.
- searches.jsonl: actual searches made by msearch.py, incorporated into the item without replacing inherited searches.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, weakly-etale refinements, ind-etale covers and Cech terms. RingHom.WeaklyEtale.exists_indEtale_comp and the affine comparison module cover ingredients, not this entire assertion over non-affine qcqs schemes, so no attachment is claimed.

## WANTED

None.

## Corrections and scope

No statement dispute and no statement change. The imported statement properly distinguishes local affine charts from a globally affine Cech product. The split constructs stronger data: D_a maps by an affine ind-etale map onto a chosen affine open U_a of U, and its composite with an affine open of V is ind-etale. Those stronger data are established in the item's first step, not assumed from a definition or hidden in a new node.

The Cech induction uses D_a -> U_a, not a false identification of products over U and V. At a projected point, shrink a previous affine ind-etale chart T to an affine open T' inside its inverse image of U_a; then T' times_{U_a} D_a is affine ind-etale over T' and hence over the already chosen affine open of V. This gives an actual open cover. Quasi-compactness permits a finite subcover only after these charts have been constructed.

The proof is marked agent-written because Bhatt–Scholze states the local refinement but does not state this particular finite Cech packaging. It follows Theorem 2.3.4, Proposition 2.3.3(4), and Remark 4.1.3 with explicit local induction. No SGA route is used. The compactification-unit and chapter routes are unchanged; the geometric inputs from other units are declared as generic tool uses in split_report.

## Not duplicates

No new nodes. Reused the existing refinement theorem, weak-etale/ind-etale permanence, finite affine-cover and intersection facts, finite affine tensor base change, and the stronger algebraic-space qcqs-product theorem. Blueprint searches for ind-étale, ind.etale, fibre products and quasi-compactness found ingredients but no blueprint node stating this whole result. The nearest blueprint ancestor is det-sf-comp-coherence-cocycle; its current latest proof's Refinement isomorphisms paragraph was read, and from.place identifies the descendant geometric refinement supporting that paragraph.

## Review by NK

I read the stage-1 brief, stages/1-dag.md, the three blueprint levels in SETUP, GOAL, the chapter and unit records, and both copies of delivery-errors B–E. I read Bhatt–Scholze's actual PDF via pdftotext at §2.3, Theorem 2.3.4, Proposition 2.3.3, Definition 4.1.1 and Remarks 4.1.2–4.1.3. I also read the Stacks source schemes.tex at Tags 01I4 (lemma-fibre-product-affine-schemes), 01JO (lemma-fibre-product-affines), 01IT (lemma-basis-affine-opens), and the open-fibre-product lemma, and proetale.tex at Tags 097J/097K for ind-etale base change and composition. These give the affine geometry used in the induction; the cited DAG statements, rather than bare tags, carry the proof dependencies.

Step 1 uses the finite-affine-cover lemma twice and the definition of quasi-compact b. Weak-etale Zariski locality and the affine-chart clause of det-pe-morphisms-etale-comparison identify the ring-map hypotheses of sk-thm-pe-indetale-refinement. I opened that node: it supplies both ind-etaleness of B_a -> C_a and of A_a -> C_a, and faithful flatness of the former. This is exactly the extra relative information the Cech induction needs. sk-def-pe-morphisms and the small-index lemma supply the small presentations; no arbitrary large index category is introduced.

Step 2 verifies the full covering definition, rather than just joint surjectivity on U. I checked the faithful-flat spectrum-surjectivity statement and the pro-etale covering definition verbatim. Quasi-separatedness of U and pqf-lem-qs-intersection-qc make W intersect U_a quasi-compact. lem-pqf-finite-affine-cover-qc-open then supplies finitely many E_ar. The singleton case of lem-sbc-finite-affine-tensor-base-change makes each inverse image affine; the point lifting argument establishes its image equals E_ar. Open immersions are etale by lem-weil-pbc-open-immersion-etale, and det-pe-morphisms-etale-comparison explicitly makes them weakly etale. The stability node supplies composition. Thus each hypothesis of the covering definition is met.

Step 3 applies lem-sfb-space-qcqs-source-products only to qcqs schemes viewed as represented spaces over Spec Z. I opened the affine-test and algebraic-space fibre-product nodes as well: the former explicitly compares representable quasi-compactness with scheme quasi-compactness, and it applies to diagonals to compare quasi-separatedness. The latter gives the sheaf fibre product, which represents the same pairs of scheme maps. Affine qcqs is the statement of lem-weil-pbc-affine-scheme-qcqs. This avoids silently treating an algebraic-space convention as an additional hypothesis.

Step 4 uses exactly affine base change and composition from sk-lem-pe-weakly-etale-stability. I checked that these clauses are in its statement. T' is chosen inside T intersect P^{-1}(U_a), so both maps in the fibre product have the same affine target U_a. The cited singleton tensor base-change statement gives affineness. The etale open immersion T' -> T has a constant small inverse-limit presentation; between affines this is affine pro-etale by sk-def-pe-morphisms. Composition then gives the actual factorization over the previous affine target V_T. Openness follows from restricting the first projection to the open T'. This is one affine-local induction, not a separate unproved comparison lemma.

Step 5 is the elementary finite-subcover argument applied to the cover actually constructed in step 4. The small-index lemma and definition of affine pro-etale say precisely what the concluding ring presentations are. All five steps are below 2000 characters, and no inline subclaim with an omitted proof is hidden by a long step.

I checked empty U, empty V (then U is empty), zero rings, n=0, repeated indices, and non-separated but quasi-separated U and V. Empty covers and empty affine charts cause no exceptions. In particular I never assume an intersection of affine opens is affine; finite affine refinement uses quasi-separatedness only for quasi-compactness. No assumption on coefficients, contractibility, finite type or Noetherianity appears. The inductive argument does not require separatedness of b or of the ambient schemes.

I read the actual Mathlib-search results. The two semantic phrasings returned ordinary etale sites, affine cover infrastructure and affine transition-limit auxiliaries; Loogle returned no hits. The grep hits in Morphisms/WeaklyEtale.lean give the definition, flat diagonal and stability, not ind-etale refinement. I opened that source and the nearby quasi-compact/quasi-separated sources. Existing project code supplies the ring refinement and affine-site ingredients but no declaration of the whole item. Consequently no Mathlib match is claimed and no duplicate or elementary new node was created. citations.json uses verbatim node statements, not reconstructed paraphrases.

## Unfinished work

None in this one-level split. No Lean files were written or compiled. The required server review_split check passed before the full delivery dry run.
