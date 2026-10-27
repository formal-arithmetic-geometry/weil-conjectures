# O1 stage-1 report: lem-sfb-kummer-normalization-boundary-etale

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kummer-normalization-boundary-etale.json: statement; split into seven steps using existing nodes. Statement unchanged. Retains the original source, blueprint provenance, historical searches and creation record, and records the additional actual searches.
- citations.json: one entry for every step/node citation, quoting the cited statement verbatim, including its hypotheses.
- report.md: this report. searches.jsonl retains the earlier attempt's search and the additional logged searches.

New nodes: 0. New Mathlib leaves: 0. The split reuses the existing DAG rather than creating special cases of its generic local-algebra lemmas.

## Attachments

None. I searched the project source for the exact blueprint tag, the item name and Kummer/normalization/boundary and Abhyankar/tensor-factor notions. No project declaration supplies all of this item's global finiteness, individual local differential vanishings, product flatness/differentials and etale source-neighbourhood clauses. In particular, RingTheory.dvr_galois_normalization_ramification_dvd and RingTheory.dvr_tame_tensor_factor_formallyUnramified are smaller inputs, attached to their existing nodes, not attachments for this whole item. Their source files are lean/WeilConjectures/RingTheory/DvrGaloisNormalizationRamificationDvd.lean and DvrTameTensorFactorUnramified.lean; I read their statements and proofs.

## WANTED

None. The ILO volume and Stacks source used here are present.

## Corrections and scope

There was no prior sandbox split or report, only one logged LeanFinder search, which I retained and read. The repository item was unsplit, with no repair note. I found no false or ill-typed assertion and changed no statement or hypothesis. In particular I did not assume excellence, regularity of B, separability of E/K, or a Galois condition on F_a/E. The existing tame tensor-factor theorem takes a finite faithful DVR map, not necessarily a standard parameter-root presentation, which is exactly the abstraction needed here.

The previously empty proof is now an assembly with explicit canonical maps. The passage from L_j tensor_V A to L_j tensor_K E uses the finite-domain linear-algebra argument written in Step 2. The passage from a global integral closure to the boundary normalization is the actual localization of the subring of F_a, not an unspecified isomorphism. The product-localization argument uses the coordinate idempotents, and base localization for differentials is proved by the Leibniz rule. None of these elementary calculations is made into a new node.

## Mathlib searches

I read the earlier logged search results before extending them. The required msearch wrapper ran LeanFinder with two wordings, Loogle with `"ramificationIdx", "Etale"`, grep with `Abhyankar|tame.*tensor|tensor.*tame|ramificationIdx.*[Ee]tale`, and LeanSearch with the finite-Galois/DVR formulation. All services answered; unavailable was not misreported as absence. The raw responses in searches.jsonl are recorded faithfully in the item, alongside the inherited records. The returned ordinary etale/unramified base-change declarations assume the input already has that property. Equality/multiplicativity formulas for ramification and residue degrees do not give Abhyankar's ramification removal. The different-ideal criterion characterizes unramified primes but does not establish the required condition after normalized base change. I also read the Etale/Basic and Unramified/Basic source around these notions. These results do not make this multi-step item a Mathlib leaf.

DAG searches by tags 09EB, 0BRM, 032L, 0307, 08WD and by the local algebra keywords found the existing inputs used below. Blueprint searches for Abhyankar, normalized tensor and boundary ramification returned no blueprint match. The ancestor tool gives a null imported ancestor, consistently with the existing provenance; I retained the detailed from.place/via chain and same_as=[] rather than inventing an imported node.

## Not duplicates

No new nodes were created. In particular the existing lem-sbc-dvr-galois-normalization-ramification-dvd and lem-sbc-dvr-tame-tensor-factor-unramified already state the generic degree bound and tame local differential-vanishing facts. The finite-closure, closure-localization, differential-localization, PID-flatness and pointwise-etale facts also already have nodes; I cited them directly.

## Review by O1

I read coord/delivery-errors.md sections B through E in full, the stage-1 brief and stage document, the three blueprint levels in SETUP.md, GOAL.md, and the item's chapter/unit records. This is a generic local-algebra input below the coefficient-specific direct-image route, not a change to that route. The three non-Mathlib off-unit inputs are declared in split_report.tool_uses with their purpose. I did not edit chapter/unit records, Lean, the shared repository or launcher scripts.

For the source, I read ILO IX Proposition 2.1(i) and its local Kummer description on printed pp.133-134 (PDF pages 139-140). Its codimension-one ingredient is expanded using the Stacks route: more-algebra.tex Tag 09EB, lemma-galois-conclusion; Tag 0BRM, lemma-abhyankar; and algebra.tex Tags 032L, 0307, 00FP, 00RT, 00U6 and 08WD, with their displayed labels. I read these local source statements and the relevant arguments. The proof is marked agent-written assembly of these existing lemma statements, rather than claiming that ILO states this algebraic formulation verbatim. No prohibited source is used as an input.

I opened and read every cited node's statement. The citation audit is as follows.

1. lem-weil-pbc-noetherian-normal-separable-integral-closure-finite gives finiteness exactly for a Noetherian normal domain and a finite separable extension of its fraction field. B and each F_a/E have precisely these hypotheses. Finite product module generators are explicitly inserted coordinate by coordinate. They also generate the algebra, so lem-weil-pbc-finite-type-noetherian-finite-presentation applies to B. This proves finite presentation without assuming the localized stalk itself is finitely presented.
2. No external theorem is hidden in the tensor identification: localizing the finite faithful V-module A at nonzero elements of V gives a finite-dimensional K-domain, hence a field by the injective/surjective multiplication argument. This field contains A and is inside its fraction field E, so equals E. Inverting the same elements on the L_j side and using balancing gives the canonical tensor isomorphism. The given factor-structure hypothesis makes each F_a the quotient by a maximal ideal with exactly the right A-map. This step is elementary and has no citations.
3. lem-weil-pbc-integral-closure-commutes-localization states an equality of subrings in the localized ambient algebra, not just a finiteness assertion. Apply it with B, F_a, and B minus q. These elements are nonzero in F_a; thus its ambient localization stays F_a. The actual S_a is the integral closure over A, is finite by localizing the module generators, and its prime Q'_a has contraction m_A. Iterated prime localization gives the exact A-algebra needed next.
4. lem-sbc-dvr-galois-normalization-ramification-dvd supplies both bounds at every closed normalization prime, for finite Galois L_j/K whose degree divides n. I checked that the unramified tensor-factor node asks for both of these bounds, a positive invertible n, the finite faithful DVR map, the ideal-power identity, a maximal tensor quotient with its right A-map, and finite integral closure over A. Every hypothesis is explicit in the item or Steps 1-3. Its conclusion is zero relative differentials at every prime over m_A, exactly the conclusion used. I do not infer separability of the residue fields from a definition or substitute an index bound for unramifiedness.
5. def-sc-discrete-valuation-ring explicitly makes A a local principal ideal domain. The localization of C_a injects into F_a and A injects into that field, so the annihilator calculation proves torsion-freeness directly. lem-weil-pbc-pid-torsion-free-module-flat then states precisely the required implication. No unsupported preservation-of-flatness assertion is used.
6. The coordinate-idempotent proof identifies each product local ring with one factor local ring, preserving the B- and A-maps. lem-weil-pbc-kahler-differentials-localization gives the source-localized differential module. Its statement only covers source localization, so I did not attribute base localization to it: instead the Leibniz calculation shows that a B-derivation kills inverses of B minus q. The universal property in def-weil-pbc-kahler-differentials then identifies the two modules, and Step 4 kills them. This explicitly addresses the common C4 error of asking a cited statement for more than it says.
7. lem-sc-etale-at-prime-flat-unramified-criterion states the equivalence between the principal source-neighbourhood conclusion and the two local conditions for a finitely presented algebra. I use it for the global finitely presented B-algebra C, its prime Q and its contracted prime q, using precisely Steps 1 and 6. It yields a g in C outside Q, so the final morphism is over Spec B as required, not merely over Spec A.

For small cases I checked n=1, a trivial Galois extension L_j=K, one factor, repeated factors, and a tensor product splitting into several fields. For L_j=K the closure factor is B and its localization is A, so differential vanishing and flatness have the expected identity-map form. With repeated factors the unique surviving idempotent still gives the same local ring. The product is nonempty by the nonempty family of nonzero tensor algebras. A residue characteristic dividing n cannot arise because n is a unit in V. No argument uses perfection of the residue field, so the mixed-characteristic and imperfect-residue-field cases remain within the cited tame theorem's hypotheses. Separability of F_a/E is essential to the finite-normalization input and is present in the statement.

Every proof step is shorter than 2000 characters (the longest is 1108); the seven steps contain the explicit assembly, with no new clause-restatement nodes and no cycles introduced intentionally. citations.json quotes each cited statement verbatim. The required server dry run is the final mechanical verification before direct delivery.

## Unfinished work

None in the stage-1 split. The cited existing non-Mathlib nodes retain their own proof tasks; this delivery neither duplicates nor claims to finish them.
