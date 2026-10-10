# Worker report

## Files written

- dag/nodes/sec-proper-base-change/lemma-weil-pbc-finite-refinement-etale-cover.json: repaired the induction claim, finite gluing, and graph argument in proof steps 2-5.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-radicial-etale-open.json: statement node for the degree-one radicial-etale base case; no Mathlib match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-fibre-specialization-bound.json: statement node for the strict specialization bound; no Mathlib match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-section-separated-closed-immersion.json: Mathlib leaf for closedness of a section of a separated morphism.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-presentation-map-limit-factorization.json: Mathlib leaf matching AlgebraicGeometry.Scheme.exists_pi_app_comp_eq_of_locallyOfFinitePresentation.

## Attachments

- AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale belongs to lemma-weil-pbc-finite-refinement-etale-cover (WeilConjectures/AlgebraicGeometry/EtaleFiniteRefinement.lean, lines 37-50); has sorry in slopmaster2.

## Sources and split

I read Stacks Project Tag 09Z0, Lemma 37.45.7, at https://stacks.math.columbia.edu/tag/09Z0. The local literature source named by the node was absent from this checkout. The five steps follow the published proof: finite affine reduction over a qcqs base; induction on a uniform geometric-fibre bound; Zariski-main factorisation and diagonal complement; finite gluing; and passage to a finite finitely presented stage with descent of opens and maps. The unchanged item statement agrees with its finite and finitely presented conclusion. The blueprint search found no duplicate assertion, and the imported blueprint metadata is retained.

## Review by G1

Step 1 covers T by finitely many affine opens, base changes U to each, applies the existing affine etale refinement node, and takes a finite disjoint union; this verifies its affine-base hypothesis. Step 2 states the induction claim for every qcqs X with E quasi-compact and separated; its conclusion is now finite and surjective, as the induction step proves. The empty case d=0 has X empty; at d=1, the radicial-etale-open node gives an isomorphism after surjectivity. The cited quasi-finiteness and bounded-fibre nodes provide a finite d for E to T.

Step 3 applies thm-pqf-zmt-factorization to E to X only after checking separatedness, finite type, quasi-finiteness and the qcqs base. Its finite compactification becomes schematically dense by the cited closure node. The projection P to E is finite by finite-morphism-permanence (a), hence affine and separated, so section-separated-closed-immersion makes s closed. Etale-composition-cancellation (3) makes s etale over the finite cover, and etale-morphism-open-map makes its image open. These two cited statements give the clopen decomposition; the etale-section-clopen-immersion citation was removed because P to E is not etale. The base-change and specialization nodes give the strict fibre bound over V. I checked W to V is quasi-compact and separated and V qcqs before the induction is used.

Step 4 uses the induction hypothesis on W to V with bound d-1, giving finite surjective Z to V. Finite implies finite type, and the quasi-compact open immersion V to the finite cover preserves the separated, finite-type and quasi-finite hypotheses needed for thm-pqf-zmt-factorization. Its second application gives finite Z' over the finite cover; the closed complement C is finite there too. For affine rings A to B to D, generators of B over A times generators of D over B generate D over A; hence the two composites to X are finite. Their finite coproduct is finite and surjective because Z' covers V and C covers its complement. The local lifts through W or E close the induction. Applying the claim at the bound from step 2 to E to T gives finite surjective T' to T locally factoring through the original U. The prior integral-transitive citation was removed because it did not establish finiteness.

Step 5 begins with that finite, hence integral, T' to T. The integral-limit node supplies finite finitely presented stages; clauses (1) and (3) of pqf-lem-limit-qc-open-descends handle the chosen opens and their limits; finite-presentation-map-limit-factorization descends the maps; and clause (3) of spectral open descent gives a covering at one stage. T_i to T is surjective because T' to T_i to T is. I checked the new radicial-etale-open statement against Tag 025G, including the identity and empty-scheme cases; the fibre-specialization statement against Tag 09Z0 and its cited specialization lemma, including a constant finite etale cover and an empty special fibre. Neither unsplit node has proof text. I checked the Mathlib leaves against Separated.lean:242 and AffineTransitionLimit.lean:1231. The node JSON parses and each step's cited statements support the uses described above.

## Cross-unit tools and route notes

The split_report declares the cross-unit black-box tools with the required why key: lem-weil-pbc-etale-ring-map-quasi-finite, lem-weil-pbc-lqf-qc-source-bounded-fibres, thm-pqf-zmt-factorization, lem-weil-pbc-fibre-degree-base-change, lem-weil-pbc-integral-morphism-limit-of-finite, pqf-lem-limit-qc-open-descends, and lem-weil-pbc-spectral-limit-descend-opens. These are inputs of the Tag 09Z0 route.

## WANTED

None. The Stacks and Mathlib sources were available locally.

## Corrections

Return point 1 (D3): step 2 now claims a finite surjection, step 4 derives finite Z' amalg C to X and applies the claim to E to T, and step 5 alone imposes finite presentation. Return point 2 (C4): step 3 removes the inapplicable clopen-section node from its text and dependencies, proves openness via the etale open-map node and closedness via the separated-section node, and spells out why P to E is separated. The earlier affine-cover, ZMT, map-limit, open-descent and report corrections remain in place.

## Unfinished

The four new nodes are leaves or unsplit statements as required for this stage. No further gap identified in this split.
