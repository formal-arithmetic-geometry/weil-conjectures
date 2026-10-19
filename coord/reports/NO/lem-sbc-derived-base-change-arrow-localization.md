# Stage-1 report: lem-sbc-derived-base-change-arrow-localization

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-derived-base-change-arrow-localization.json`: statement, split; seven proof steps using existing nodes only. Not a Mathlib leaf.
- `citations.json`: 22 verbatim statement excerpts, one for every step/node citation.
- `searches.jsonl`: six searches actually performed by msearch.py during this attempt; the item's inherited search records are retained.

New nodes: 0. Mathlib leaves created: 0.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and the notions baseChange/restriction/localization/counit. Read `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Locality.lean`, including `AlgebraicGeometry.Etale.baseChange_app_paste_horiz` and the locality API, and inspected the declaration of `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale` in `SixFunctors/BaseChange/EtaleDerived.lean`. These use `DerivedCategory.Plus`; the item quantifies over arbitrary unbounded K and all integer q, and also asserts a specific equality under fixed comparisons. They do not supply an exact attachment, even if their proofs are closed. No upstream master sorry declaration was treated as evidence of completion.

## WANTED

None. The source required for the argument is available locally.

## Corrections and mathematical scope

The item was unsplit and had no proof. Its mathematical statement is retained, including abelian sheaves, arbitrary unbounded K, the particular counit-transpose base-change map, its canonical comparison arrows, naturality, and every integer q. No properness, smoothness, qcqs, torsion or boundedness assumption is added. I made the statement's implicit inverse-image composition dependency explicit and replaced `lem-weil-pbc-site-morphism-composition` in stmt_deps by the more precise `lem-weil-pbc-inverse-image-composition`, which actually states the abelian-sheaf comparisons. The statement also explicitly names the existing etale inverse-image/restriction node.

The point not to suppress is compatibility of arrows: isomorphisms between source objects and between target objects do not identify the exchange map. Steps 2 and 3 give the square-isomorphism and counit equations; steps 4–6 calculate the transposes. In particular I did not cite the bounded-below `lem-weil-pbc-etale-localization-exchange`, or the bounded-below `lem-weil-pbc-derived-exchange-termwise`, for an unbounded assertion.

The source in etale-cohomology.tex, Tag 0EZR, `lemma-base-change-local`, explicitly treats arbitrary K in D and calls on sites-cohomology.tex, Tag 0D6G, `lemma-restrict-direct-image-open`, for the derived local identifications. The arrow computation is implicit there, so proof_origin is marked agent. Its construction is the counit-transpose formula of Tag 07A7, `remark-base-change`. The local K-injective argument in 0D6G has no boundedness restriction. The current main-20261015 blueprint ancestor's clauses (2) and (3), and unit sk-def-bc's etale-localization compatibility, are exactly what this item serves. Its chapter and unit are unchanged; it is not the unit's key statement, so no unit file is written.

## Mathlib and duplicate searches

Ran the required leanfinder, loogle, grep and leansearch searches with msearch.py and read their returned hits. A second semantic phrasing found generic `CategoryTheory.Adjunction.derivedε_fac_app`, `derivedη_fac_app`, `derived`, and derived comparison maps. I read the derived counit/unit formulas in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:103–129 and the composition counit in Mathlib/CategoryTheory/Adjunction/Basic.lean:565–582. They concern abstract derived adjunctions, not the full geometric site localization comparison of this item. The first semantic query returned etale morphism stability and unrelated ring results. LeanSearch returned sheaf pushforward/pullback and over-site functors. The Sites grep returned sheafification localization and covering stability; the derived-category grep returned zero hits. None is an exact match or a one-line specialization giving the complete item. All six queries and their real results are recorded without inventing a search.

Searched the whole DAG by the tags 0EZR/07A6, by restriction/localization/counit, and by inverse-image and composition-coherence filenames. Read the existing underived `lem-sbc-base-change-arrow-localization`, the bounded-below etale-localization and termwise-exchange nodes, and all the statements cited below. Ran blueprint_refs.py ancestor for the item, and whole-blueprint searches for counit-transpose and localization of the base-change, as well as broader locality/base-change queries. No other blueprint node states this exact unbounded arrow identity. Existing generic coherence and slice-localization nodes provide every auxiliary assertion; no new lemma is necessary. In particular I did not create a new node for the short formal transpose calculation.

## Not duplicates

No new nodes, hence no new/existing node pairs to distinguish. The underived arrow-localization node does not imply this unbounded derived assertion. The ringed derived slice-localization node supplies comparison functors and adjunction compatibility, not this four-sided base-change arrow identity; it is used as a dependency.

## Review by NO

I read the worker brief, the three blueprint levels in SETUP, the chapter sec-smooth-base-change, unit sk-def-bc, GOAL and dag-sync, stages/1-dag and all of delivery-errors B–E. I checked the mathematical source by reading the entire proof of Stacks 0EZR in etale-cohomology.tex, the construction of the unbounded base-change arrow in 07A7 and proof of 0D6G in sites-cohomology.tex, and the localized morphism construction in sites.tex at `lemma-localize-morphism-strong`. No SGA route is involved. There are no new nodes requiring additional source audits.

Step 1 uses `lem-weil-pbc-etale-base-change-finite-limits` clause (1) to see that c and d are etale, `lem-weil-pbc-etale-site-localization-open` for the actual equivalences of etale sites with slices, and `lem-weil-pbc-etale-inverse-image-restriction` for the natural abelian-sheaf restriction identification. The projections of the two fibre products explicitly give Y_U = U times_B T_B. `lem-weil-pbc-inverse-image-composition` gives the normalized inverse-image maps, while `lem-weil-pbc-ringed-derived-slice-localization` states both displayed unbounded derived slice comparisons and their adjunction compatibility. These are precisely the maps called p_g and p_h in the proof; the localizing objects are B for g and U for h, whose preimages are T_B and Y_U. The arbitrary U->B does not need to be a Cartesian base change of f: its inverse-image comparisons follow from fa=bf_U.

Step 2 uses `lem-weil-pbc-direct-image-composition-coherence` for the associativity of the fibre-product direct-image comparisons, and `lem-weil-pbc-inverse-image-composition` for their unit-normalized conjugates. `lem-trf-adjoint-composition-coherence` allows nonidentity right-adjoint composition isomorphisms, so its hypothesis fits these actual fibre-product isomorphisms; I deliberately did not use the narrower theorem requiring literal equality of right adjoints. The etale inverse-image/restriction identification is from the node just named. Each path is a rebracketing along the explicitly written equal composite scheme map. `prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-site-restriction-exact` and `lem-weil-pbc-exact-functor-complex-cohomology` ensure the termwise functors preserve quasi-isomorphisms. Clause (2) of `lem-weil-pbc-localization-universal-property` expressly preserves natural-transformation composition, so the sheaf coherence equation descends to the unbounded category. This cites actual statements rather than a convention hidden in a definition.

Step 3 takes exactly the final sentence of `lem-weil-pbc-ringed-derived-slice-localization`: compatibility with the derived adjunction units and counits. The displayed equation is that counit compatibility with its domain and target written. The hypothesis is a morphism of ringed sites with a specified object downstairs; g, B and T_B provide it. Coefficients are the constant Z throughout; no change from abelian sheaves to a different coefficient category is made.

Step 4 is a substitution, not an independent lemma: naturality of alpha_e, the counit equation in step 3, the inverse-image coherence equation in step 2, and naturality of theta_U give the displayed formula. The cited `sbc-def-base-change-map` states exactly the inverse-image square and its counit-transpose definition in the unbounded module category, specialized to Z. I wrote which naturality moves the particular map p_g, rather than claiming that the maps simply transport.

Step 5 again uses the stated derived unit/counit compatibility of `lem-weil-pbc-ringed-derived-slice-localization`, now for h at U. I checked that its equation goes from r_YU h^-1 Rh_*M to r_YU M; kappa is inverted in the subsequent expression because the local transpose starts with h_U^-1 r_U A. Naturality of the local counit, this equation, and naturality of kappa give the explicit transpose calculation. The use of `sbc-def-base-change-map` here is its canonical derived adjunction, not a bounded-below substitute.

Step 6 uses the defining transpose in `sbc-def-base-change-map` and the bijective mate correspondence explicitly stated by `def-weil-pbc-adjunction-mate`. After step 4 both local transposes are the very same morphism t_U followed by h_U^-1(C_L). Thus equality follows from the adjunction bijection; it is not inferred from an object-level isomorphism. All the comparisons and mates are natural, so the same calculation is natural in K.

Step 7 uses precisely exactness of restriction from `lem-weil-pbc-site-restriction-exact`, the natural cohomology isomorphism for every integer from `lem-weil-pbc-exact-functor-complex-cohomology`, and composition-preserving descent from `lem-weil-pbc-localization-universal-property`. This yields the equation of cohomology arrows, not merely identifications of cohomology objects. No positive-degree or bounded-below condition has been inserted.

I checked the empty etale object (all restricted objects and maps are zero), identity localizations (all comparison maps reduce to identity comparisons), g or h an identity (the corresponding counit is the identity under the canonical identity comparisons), K=0, and K a shift of a sheaf, including negative shifts. The equations retain their types in every case; none requires q>=0. The two elementary steps are substitutions using the already written equations and the definition of transpose; no non-elementary theorem is concealed in them. Every proof step is shorter than 2000 characters. I checked that no selected dependency reaches the item and created no circular descendant. All 22 citations.json quotes are literal substrings of the cited statements.

Generic off-unit infrastructure is declared in split_report.tool_uses with its exact role. It verifies the unit's prescribed localization route; it does not replace that route. No statement dispute or source error was found.

## Unfinished work

None in this one-level split. The cited unsplit existing infrastructure remains its own stage-1 work; no new unsplit node is introduced by this delivery.
