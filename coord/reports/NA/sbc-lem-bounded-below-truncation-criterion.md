# Worker report

## Files written
- dag/nodes/sec-smooth-base-change/sbc-lem-bounded-below-truncation-criterion.json: item split, no Mathlib match.
- citations.json: verbatim statement quotations for all proof-step citations.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments
None attached. The second reader found tagged candidates in the supplied Lean checkout; see the second-reading audit below. Concept searches found single-object nonnegative right-derived cohomology and truncation ingredients, not a Mathlib declaration of all clauses of this item. Master sorry declarations were not treated as proofs.

## WANTED
None.

## Statement clarification and proof repairs
STATEMENT-DISPUTED: the imported statement binds only K and n; g and h and the phrase “after pullback” are unbound. Read literally, Rg_*K is ill-typed without a domain for g. The source paragraph and the bounded-below smooth-base-change neighbour fix the intended square. The corrected statement introduces g:T→S, f:X→S, Y=T×_S X, e:Y→T, h:Y→X and writes the three canonical maps. No coefficient-category substitution was made: these are abelian etale sheaves with allowable torsion, not modules or condensed sheaves. Smoothness and qcqs play no role in this truncation fact and were not hypotheses of the imported item.

The original proof went from diagonal support straight to the canonical map being an isomorphism. Knowing only the image filtration does not prove its kernel is zero. I replaced this inference by the existing thm-sp-truncation-e2 part 5, which explicitly states the isomorphism of c_n, and expanded the two analogous clauses. The existing hypercohomology-filtrations node is more than its title suggests: its statement includes the three spectral sequences and ranges, so it is legitimately used in step 1.

## Search audit
Read the chapter and sk-rem-rest unit: the unit has no proof steps and lists the derived/bounded-below continuation. The proof keeps the item's stated spectral-sequence route. Ran blueprint_refs search for truncation and bounded-below truncation, ancestor for the item, and whole-DAG concept searches. Found the existing thm-sp-truncation-e2, hypercohomology-filtrations, standard t-structure, exact inverse-image and exact-functor cohomology nodes; no new node was needed. same_as is empty: no other blueprint node states exactly these three specialized canonical maps; the general theorem is a reusable tool.

The seven msearch calls are recorded verbatim in the item. LeanSearch returned HTTP Internal Server Error and is marked unavailable. LeanFinder's two phrasings returned exact-functor Ext, derived-functor definitions and truncation/representative results, which do not state the derived comparison. Loogle returned no combined truncation/right-derived result and then rightDerivedFunctorPlus definitions. Grep found truncation homology ingredients. Read Mathlib Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean (definition at line 37) and Embedding/CochainComplex.lean (quasiIsoAt_ιTruncLE at line 57, quasiIso_ιTruncLE_iff at line 280): those compare an underived complex or define the functor, and do not directly specialize to this item.

## Review by NA
I read the item's master blueprint paragraph, the sec-smooth-base-change chapter and sk-rem-rest unit, and Stacks 015J, derived.tex, lemma-two-ss-complex-functor: the latter assumes a left exact functor and bounded below complex and gives the E2 terms, bounded convergence and finite filtrations. It supports the blueprint spectral-sequence route but is not cited as if it alone asserted injectivity of the canonical truncation map. There are no new-node sources to review.

Step 1 uses the standard t-structure's explicit representative characterization and the hypercohomology-filtrations statement's three displayed sequences and diagonal ranges. The renaming (f,f′,g,g′)=(g,h,f,e) matches the square including domains. A cohomological lower bound a exists by D+; the allowable torsion restriction supplies the torsion hypothesis of that node. The arithmetic p+q=n and p≥0 is written out.

Step 2 uses the entire hypotheses and the canonical c_n assertion in thm-sp-truncation-e2 part 5. I opened def-sp-etale-dictionary: its statement really identifies Ab(X_et) as Grothendieck, f_* as left exact additive, and the K-injective computation as Rf_*. Thus all abstract hypotheses hold for g_*; no small index category or unstated flatness is introduced. This is an existing general tool, not a new restatement of the item.

Step 3 uses inverse-image-exact for exactness and exact-functor-bounded-below for the natural H^n(F L)≅F H^n(L) comparison. Naturality identifies the map, not just its source and target objects. Applying the functor to c_n and its inverse is the elementary argument explicitly written there.

Step 4 uses inverse-image-exact for preservation of kernels, derived-inverse-image for the termwise representative, and the standard t-structure for the kernel formula for τ≤n. Their statements suffice to identify the truncations and inclusion maps, rather than appealing to an undocumented compatibility theorem. The same existing general truncation theorem with the dictionary applies to h_* and the bounded below complex e^-1 K; no claim that pushforward preserves allowable torsion is needed.

Checked edge cases K=0, n<a, K concentrated in degree n, and K concentrated in degree n+1. For n<a all diagonals are zero; for the last case τ≤n K=0 and left exact derived direct image has no cohomology below n+1, as encoded in the cited spectral-sequence theorem. Negative n is allowed throughout. The cutoff kernel and all maps use the cohomological, not stupid, truncation. No new unsplit node, circular citation, hollow definition, missing smaller lemma or changed coefficient category was introduced. The original shorthand and the unsupported kernel inference were the corrections made on this reading.

## Unfinished
None; the fresh second reader still reviews and delivers. No Lean file was written or compiled, no agent was started, and no push was requested.


## Second reading by NA

- Item statement: compared the master blueprint node, its entire proof paragraph, sk-rem-rest, the chapter, and the neighbouring sbc-thm-bounded-below-derived-smooth-base-change square; PASS. The reported STATEMENT-DISPUTED binding repair is faithful: K is on T, g maps T to S, f maps X to S, h maps Y to X, and e maps Y to T. No smoothness, qcqs, or invertibility assumption is needed for truncation; allowable torsion remains the original restriction.
- Step 1: opened def-sbc-standard-tstructure-derived-category and all three clauses of def-weil-pbc-hypercohomology-filtrations, and derived.tex Tag 015J, lemma-two-ss-complex-functor (lines 7176–7251); PASS. The dictionary renaming (f,f',g,g')=(g,h,f,e) has the correct domains. The allowable-torsion definition places K in D+ with torsion cohomology, so the cited node's hypotheses hold. Bounded-below representatives and the finite diagonal a≤q≤n are supplied by the cited statements; p≥0 implies q=n−p≤n.
- Step 2: opened thm-sp-truncation-e2, especially its hypotheses and part 5 defining c_n, and def-sp-etale-dictionary; PASS. The canonical inclusion, not an unspecified object isomorphism, is the theorem's map. Both sheaf categories are Grothendieck and g_* is left exact additive; no extra scheme hypotheses occur.
- Step 3: opened prop-weil-pbc-inverse-image-exact and lem-weil-pbc-exact-functor-bounded-below, including its naturality clause; PASS. Naturality identifies the map with f^{-1}(c_n). Applying f^{-1} to the two inverse identities proves invertibility in two lines, so the elementary designation is justified relative to these citations.
- Step 4: opened the exact inverse-image, termwise derived-inverse-image, standard t-structure, truncation theorem and etale dictionary nodes; PASS. Exactness preserves the cutoff kernel, other degrees and differentials are termwise identical, and this identification preserves the inclusion. The bounded-below representative e^{-1}K has terms zero below a, and h_* satisfies the same abstract hypotheses, so part 5 gives precisely the third canonical map.
- New nodes: none; PASS B1–B7 and the duplicate/restatement audit vacuously. No extra lemma is required: the reusable general truncation theorem is strictly more general than this specialization. Its use across units is already explained as a tool in the report, for the maintainer to decide.
- Citations and cycles: independently checked all eleven quotes against the full current cited statements; all are verbatim. Traversed statement and proof dependencies of each cited node: none reaches this item, so the repaired proof introduces no cycle.
- Edge cases: PASS for K=0 and the empty scheme (all maps are 0→0); over a field for K concentrated in degree n or n+1, including n=0 and n=1; and for every negative n and n<a. The degree-n+1 case has zero degree-n direct-image cohomology by the nonnegative-p range. No stupid truncation is substituted for the canonical kernel truncation.
- Independent source search: rg by the exact item id in the supplied slopmaster2 checkout found DerivedCategory.Plus.isIso_homologyFunctor_map_map_truncLEι_app in PlusDevissage.lean, lines 130–144, and AlgebraicGeometry.Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app, AlgebraicGeometry.Etale.isIso_homologyFunctor_map_baseChangeSource_map_truncLEι_app, and AlgebraicGeometry.Etale.isIso_homologyFunctor_map_baseChangeTarget_map_truncLEι_app in SmoothBaseChange/Derived.lean, lines 157–185. I read all four statements and bodies. The generic declaration requires a left-t-exactness hypothesis; the three specialized ones concern sheaves of modules over Λ, not literally the abelian-sheaf category of this node. The supplied local/sorry_map_slopmaster2_full.jsonl.gz has no records for these declarations, so it cannot certify them closed. No attachment or closure is claimed without a checked category identification and a suitable sorry audit.
- Independent Mathlib search: ran msearch grep with the broader query `isIso.*(truncLE|truncLT)|isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE`; its 25 hits and actual results are in searches.jsonl. Read TruncLEGT.lean lines 242–254 and Embedding/CochainComplex.lean lines 269–283. They characterize when the truncation inclusion itself is an isomorphism or quasi-isomorphism and require the upper bound on K; this item assumes only a lower bound and applies a right derived functor before degree-n cohomology. These are ingredients, not a leaf for this item.

Changes made: corrected the Attachments paragraph's false claim that the blueprint-tag search found no declaration; recorded the actual candidates and why none is certified as this item's finished proof. Added this independent second reading and the fresh Mathlib search log. The checked statement, four proof steps, citation quotations and first worker's Review by NA section were retained.
