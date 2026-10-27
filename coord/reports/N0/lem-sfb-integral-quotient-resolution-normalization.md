# Stage-1 delivery: lem-sfb-integral-quotient-resolution-normalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-quotient-resolution-normalization.json — statement, split into six steps; no Mathlib match for the whole statement.
- citations.json — one verbatim statement extract for every node cited by each step.
- report.md — this report. searches.jsonl contains the actual search-command results.

No new nodes and no new Mathlib leaves. The inherited statement, creation record, blueprint ancestry and original searches are retained. The added statement dependencies supply the constant sheaf, Noetherian ring, inverse limit, cochain complex, quasi-isomorphism, scalar restriction and size conventions used in the statement. No Lean file was written or compiler invoked.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, integral quotient/resolution/normalization, uniformizer, and the integral coefficient-limit declarations. IntegralCoefficientLimit.lean and IntegralCoefficients.lean treat the base field/p-adic case and do not state the whole arbitrary finite-extension, actual augmented K-flat quotient assertion. Other quotient-resolution hits concern unrelated ordinary ring/scheme Koszul resolutions. No project declaration gives all the clauses under these hypotheses.

## WANTED

None for this split. Local-field structure is used through the existing DVR and finite-quotient nodes, not asserted as a new uncited local-field theorem. Their historical source note about Serre is retained upstream and is not a newly missing source for a new node.

## Findings and changes

The item was unsplit and the sandbox had no earlier node or report. Its statement is correct and has not been changed. The main danger was losing the actual quotient projection when replacing the pulled-back condensed coefficient by an abstract inverse limit. The new step 2 uses the ordinary normalized restriction-square theorem, not just existence of a ring-sheaf isomorphism. Applying that square to the regular finite module, its identity underlying map is linear for both integral actions. Acting on the unit yields the equation between the actual quotient map and the transported limit projection. This is also what identifies the particular cokernel projection in step 5.

The source for the item is paragraph (1) of the current blueprint integral proper-base-change proof. I also read the current blueprint integral coefficient-limit statement and all four proof steps, Stacks sites-modules.tex Tag 093M (lemma-completion-flat), Tag 093J (lemma-constant-exact), and sites-cohomology.tex Tag 06YQ (lemma-bounded-flat-K-flat). The proof is marked agent-written because the normalized action-on-one argument and assembly are written out here; the blueprint alone did not contain those details. No SGA source is used.

DAG searches included the Stacks tags 093M, 093J, 06YQ and the statements concerning continuous integral coefficients, quotient projections, finite-free cokernel resolutions and scalar flatness. blueprint_refs.py searches included completion, uniformizer, 093M, finite quotient, integral-limit, uniformizer quotient, finite-constant; its ancestor command confirms det-thm-sfb-proper-base-change-integral through lem-sfb-integral-quotient-direct-image-comparison. No blueprint node states the whole item. The existing nodes were sufficient, so I did not create any elementary facts, duplicate lemmas or replacement clauses.

Five fresh Mathlib searches were run using msearch.py: Loogle for AdicCompletion and Flat, two differently phrased LeanFinder searches for the sheaf quotient/resolution statement, LeanSearch for the normalized inverse-limit quotient augmentation, and grep for KFlat/kFlat/completion flatness. All services answered. The relevant hit AdicCompletion.flat_of_isNoetherian was read in Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean, lines 378–381. It is ordinary ring completion flatness; it does not give the pulled-back ring-sheaf comparison or actual quotient augmentation. Profinite limit hits likewise do not give this statement. The original item's searches are preserved, and each newly recorded query exactly matches searches.jsonl.

## Tool uses

The local-field DVR theorem, ordinary normalized integral/finite encoding comparison, completed-constant flatness and quotient theorem, flat-scalar nonzero-scalar monomorphism theorem, and exact tensor internal/section equivalence are generic tools. They do not replace proper base change, the torsion-free cone route, or any unit-level reduction. The split_report.tool_uses field records off-unit statement uses for maintainer review. The rank-one free-cokernel resolution is already in this chapter and is a generic lemma for arbitrary commutative ring sheaves.

## Not duplicates

No new nodes were created. In particular I reused lem-sfb-finite-free-mono-cokernel-kflat, lem-sfb-flat-scalar-cyclic-resolution and lem-weil-pbc-constant-completion-equivalence instead of creating narrower variants of 06YQ or 093M.

## Review by N0

I checked B through E of delivery-errors.md against the item, the open cited statements and the source texts. There are no new statement-only nodes to check for independent hypotheses, tagging, duplicates or hidden proof sketches. The item retains its positive level convention j >= 1 and the fixed uniformizer. Its blueprint.from.place already names paragraph (1); the report specifies exactly the cone argument realized there. Every step is under 2000 characters.

Step 1 uses lem-weil-l-adic-extension-integers-dvr for the PID, domain, nonzero uniformizer and finite residue field; its five clauses actually contain these facts. lem-weil-pbc-pid-noetherian-normal supplies Noetherianity, and lem-weil-valued-dvr-finite-quotients supplies finiteness and quotient transitions. Their hypotheses match the given extending absolute value and valuation ring. The scalar resolution itself is written out from injective multiplication in a domain and the definition of the quotient; no extra resolution node was made.

For step 2 I read the statement of lem-pe-integral-normalized-restriction-squares and both encoding definitions. The theorem gives the integral encoding, finite encodings for all positive levels, and identity underlying section-action comparisons. The integral encoding includes the ring-sheaf isomorphism to the completion; the finite encoding includes the constant-section-normalized ring-sheaf isomorphism. Index n=j-1 is valid because j >= 1. The proof extracts the coefficient equation by evaluating linearity of that identity map on the regular finite module at its unit. It does not take a construction from another node's proof or assume inverse image preserves arbitrary inverse limits. There is no finite-type, characteristic, constructibility or properness hypothesis in the cited ordinary theorem. The small-site universe convention is the one already in the statement dependencies.

Step 3 uses only the flatness and canonical quotient sentence in lem-weil-pbc-constant-completion-equivalence. The statement quantifies over every small site, commutative Noetherian ring and finitely generated ideal, so the pro-etale site and principal ideal (pi) qualify. Its displayed quotient is induced by the projection, exactly the required normalization; no equivalence of the constant and completed ambient module categories is claimed. The proof verifies that alpha carries the actual constant-scalar map to the canonical one by checking every finite projection. I read Tag 093M's canonical quotient formula, including its proof, rather than using an unsupported claim about inverse limits. All powers are covered by the theorem, as also follows from cofinal powers for I^j.

Step 4 takes only the injectivity sentence from lem-sfb-flat-scalar-cyclic-resolution. The nonzero scalar, domain and specified flat constant-algebra structure have been proved in steps 1 and 3. Its exact sequence uses the actual cokernel map already fixed in step 3. Step 5 then applies lem-sfb-finite-free-mono-cokernel-kflat with both ranks equal to one. Its statement explicitly gives the specified augmentation, degree-zero projection, flat terms and K-flatness; it is not merely a definition of K-flatness. The proof checks the +pi^j differential and q pi^j=0 and spells out the degree -1 and degree 0 cohomology, so the conclusion fixes the map and not only an abstract isomorphism class.

For step 6, def-weil-pbc-internal-abelian-sheaf-module-equivalence alone only preserves underlying abelian sheaves. I therefore also cite lem-pe-internal-section-tensor-comparison, whose statement explicitly asserts exactness, the tensor and regular-module comparisons, and preservation/reflection of acyclicity, flatness and K-flatness on total complexes. This repairs the possible C4 gap of asking a definition node for a tensor or K-flatness theorem. The small site and abelian sheaf tensor assumptions are the fixed project constructions. As the underlying maps are unchanged, the augmentation remains the actual q in both presentations.

I checked the empty scheme (the sheaf category is trivial and all assertions remain valid), the first level j=1, the unramified base example E=Q_l, and arbitrary ramification. The finite coefficient can have zero divisors, but no injectivity of pi on A/pi^j is asserted: regularity is only on A and R_T. Zero terms of the two-term complex cause no problem. No assertion is made at j=0, and no inverse-limit exactness is presumed. There is no hidden boundedness requirement on ambient complexes, no use of completed tensor in the ordinary derived category and no cycle through the direct-image comparison item. citations.json contains a literal extract from every cited node's current statement.

## Unfinished work

None in the one-level split. Server dry run and delivery results are recorded by the required tools after this report is written.
