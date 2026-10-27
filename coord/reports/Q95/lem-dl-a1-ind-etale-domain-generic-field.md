# Q95 stage-1 report

1. Files written: `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-ind-etale-domain-generic-field.json` — statement node, now split, no exact Mathlib match. No new nodes or new Mathlib leaves. `citations.json` supplies verbatim statement quotes for every step citation. Existing item searches are retained; five fresh searches are recorded exactly from this sandbox's searches.jsonl.
2. Attachments: none. The blueprint tag search in WeilConjectures found no declaration for this item. Concept searches and inspection of RingTheory/ProEtale/IndEtale.lean found `Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing` and residue-field separability, but neither states the canonical generic-fibre isomorphism and the map-extension assertion. They are not full attachments.
3. WANTED: none.
4. The statement is correct and unchanged. Its source metadata incorrectly locates Tag 092Q in proetale.tex: the tag table and actual statement place it in more-algebra.tex, label lemma-absolutely-flat-over-field. Proof sources record the correct file. This is a bibliographic error, not a mathematical dispute. The original node had no proof; the earlier search verdict wording ('local-ring comparison') was imprecise, and fresh verdicts specify the generic-fibre result. Maintainer-owned fields and original searches are preserved.
5. Nothing remains unfinished in this one-level split.

## Sources and route

Read GOAL.md, the stage-1 brief and stage document, SETUP's three levels, worker rules, tools documentation, and delivery-errors B–E (including the duplicated archived sections). There is no released repair note and no earlier sandbox split. Read the chapter and sk-d-dl-a1-setup unit records and the latest blueprint rem-dl-a1-conventions (now filed under sk-lem-wft-curve-heart). This is an auxiliary generic-field calculation beneath the boundary inertia comparison. It changes neither the chapter route nor the definition of unramifiedness.

For the item, read pione.tex Tag 0BSD, section-ramification, including the henselization/fraction-field diagram, plus more-algebra.tex Tags 092H (lemma-base-change-weakly-etale), 092N (lemma-when-weakly-etale), and 092Q (lemma-absolutely-flat-over-field), and algebra.tex Tag 00U3 (lemma-etale-over-field). The proof is marked agent assembly: these sources provide the input theorems, and the domain and fraction manipulations are explicitly supplied here.

The whole-DAG and blueprint searches for ind-etale, generic field, fraction field, 092Q and 00U3 located existing tools. No helper node is needed. The proof does not repackage a clause as a new node. Every step is under 600 characters, and no long step hides another lemma.

## Mathlib search assessment

The actual fresh searches comprise LeanFinder with two phrasings, Loogle on Algebra.IsSeparable and IsFractionRing, LeanSearch for the generic-fibre statement, and logged grep for ind-etale names in RingTheory. All services answered. Read Mathlib/RingTheory/Etale/Field.lean, especially Algebra.Etale.iff_exists_algEquiv_prod at line 271: it supplies the field-product theorem already represented by the existing Mathlib leaf, not the ind-etale generic-field conclusion. FormallyEtale.iff_isSeparable has an essentially-finite-type hypothesis and already takes fields; it cannot establish the needed field property. Loogle's IsIntegralClosure.isLocalization_of_isSeparable in DedekindDomain/IntegralClosure.lean assumes C is an integral closure inside an already separable extension; our arbitrary C is not assumed integral over A. No hit gives a one-line specialization of the item. Preserved searches from the item's creation are history; the new logs record the current assessment.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs.

## Review by Q95

I checked each step with the source and each cited node's statement open. Step 1 gives inverse tensor/localization formulas, rather than appealing to an uncited tensor/localization theorem. The formulas respect balancing and the ordinary fraction relation. Injection of A into C guarantees every denominator u(s) is nonzero; the domain hypothesis then proves the map into Frac(C) injective. Thus the K-algebra B really is a nonzero domain before any field theorem is used.

Step 2 uses precisely the base-change and ind-etale-implies-weakly-etale clauses of lem-weil-pbc-ind-etale-stability. The base change is along A to its genuine fraction field K. Its other input, lem-weil-pbc-weak-etale-field, explicitly states that EVERY finitely generated K-subalgebra is finite etale. This applies to K[b], without assuming that B or C is of finite type. Both statements were read in full. They are generic algebra tools from the proper-base-change unit; split_report.tool_uses explains why this unit has no replacement. Neither tool depends on this item, and this use supplies a missing algebraic detail rather than replacing the unit's geometric route.

Step 3 uses lem-weil-pbc-etale-algebra-over-field-product, whose statement explicitly permits an etale ring map over a field and gives finite separable field factors and a K-algebra isomorphism. This is the exact conclusion used for K[b]. I checked the zero-product convention: K[b] contains the nonzero field K, so the empty product is impossible. If at least two factors remain, a coordinate idempotent and its complement are nonzero zero divisors. That elementary argument, written in the step, forces exactly one factor. This is not assuming that a filtered presentation has injective transition maps or domain terms.

Step 4 takes inverses inside those actual subalgebras K[b]; hence B is a field. The cited definition def-weil-pbc-separable-algebraic-extension says every element must be algebraic and have separable minimal polynomial. Inclusion K[b] into B preserves the evaluation kernel, so its monic generator is literally the same minimal polynomial. This verifies both algebraicity and separability, not merely algebraicity.

Step 5 constructs a preimage of every c/d in Frac(C). The denominator d/1 is nonzero by step 1 and invertible by step 4. Thus the specific canonical map is surjective, not just an unspecified field isomorphism. It fixes K, so evaluation kernels preserve separability here as well. Step 6 uses the injectivity of f on A exactly to make f(u(s)) nonzero, defines the localized map by a formula, and proves its injectivity using inverses in the already established field B. It then proves injectivity on C and uniqueness on every c/d. No injectivity of f on C was assumed in defining the localization map.

I tested A=C, A already a field, the nonintegral etale domain Z to Z[1/2], an infinite separable field extension, and positive-characteristic examples. The proof allows all of these; it does not assume normality, locality, finiteness, or integrality over A. The domain assumption is essential: a product K times K would have two factors and the one-factor argument would fail. A purely inseparable field extension cannot pass the etale-subalgebra theorem. The zero-ring corner is excluded by the integral-domain convention. These checks required no statement correction. Citation quotes were taken verbatim from the actual node statements, not from their proofs; no SGA sources, Lean edits, compilers, or repository writes were used.
