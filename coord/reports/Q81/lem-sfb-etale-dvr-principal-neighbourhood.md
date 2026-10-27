# Worker report: lem-sfb-etale-dvr-principal-neighbourhood

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-dvr-principal-neighbourhood.json: statement item, now split into seven proof steps. No exact Mathlib match found. Its statement and statement dependencies are unchanged.
- citations.json: all 17 step/node pairs, with quotations checked verbatim against the current cited statements.
- searches.jsonl: six actual Q81 Mathlib search results, retained as logged by msearch.py. The item's inherited searches are also retained in its JSON.
- report.md: this report. write_split.py is a sandbox-only reproducible writer, not a delivery file.

New DAG nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, principal DVR terminology, and etale/discrete-valuation/Dedekind combinations. The existing Scheme.Etale.isDiscreteValuationRing_stalk statement in AlgebraicGeometry/Sites/DivisorMap.lean concerns stalks, not a principal localization of an arbitrary affine etale algebra with all the item's clauses. It is not an attachment for this item.

## WANTED

None. All source material used is present under literature/stacks-project/.

## What needed correction

The item had no proof and did not justify the sentence in Models Tag 0CDD that one can find a standard open which is a DVR. The split now proves the requisite finiteness and writes out the finite avoidance construction, rather than treating that sentence as an invocation of a new lemma which restates the item.

The item statement remains correct without a finite-module, henselian, excellent, or complete hypothesis. No statement correction or change to the chapter/unit route is made. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor returns None. Its precise inherited place and via chain are retained, and same_as is []. Searches for DVR and principal DVR across the blueprint found no equivalent principal-neighbourhood theorem. The unit is the inherited sk-thm-sf-ctf-stability, not a key unit node, so no unit realization file is changed.

## Source error

I read More on Algebra Tag 0AP2, lemma-Dedekind-etale-extension, together with Algebra's definition-dedekind-domain and Models Tag 0CDD, lemma-etale-local-at-worst-nodal. In the Stacks definition a field is allowed as a Dedekind domain. Thus 0AP2's product-of-Dedekind-domains assertion does not by itself exclude field factors, and its additional sentence that all maximal localizations are DVRs has a field exception. Explicitly, for a DVR R and its nonzero uniformizer pi, the etale algebra R[1/pi]=Frac(R) is a field; its maximal ideal is zero and its localization there is still a field, not a DVR under def-sc-discrete-valuation-ring. The same issue is visible in R times Frac(R).

The current item already imposes the correct closed-fibre condition. The split uses lem-sbc-etale-trait-stalk only at a point whose contraction is m_R. That statement gives a genuine nonfield DVR and injectivity at exactly such points. It does not use 0AP2's overbroad assertion for a generic-only component. No new or existing source node is edited to propagate the source error.

## Searches and reuse

I searched the whole DAG for 0AP2, Dedekind-etale-extension, normal etale factors, semilocal/Dedekind localization, finite fibres, prime avoidance, localization prime correspondence, principal open immersions, and actual affine stalks. I opened every statement cited below. In particular, lem-sc-semilocal-dedekind-dvr-reduction and lem-sc-dedekind-localization-dvr only provide prime localizations of an already specified domain, and lem-trf-etale-normal-domain-finite-factors is unnecessary for the direct finite-spectrum argument. I reuse the existing stalk theorem rather than introducing another etale-DVR node. No new nodes remain requiring duplicate or blueprint searches.

Q81 ran LeanSearch and LeanFinder on the full principal-neighbourhood statement, Loogle with the pair of name strings "IsDiscreteValuationRing", "Etale", and grep for IsDiscreteValuationRing|isDiscreteValuationRing in RingTheory/Etale. It then tried a second LeanFinder phrasing in terms of a quasi-finite algebra over a trait, and grep for isDiscreteValuationRing_of_dedekind_domain|is_dvr_at_nonzero_prime in RingTheory/DedekindDomain. All six services returned successfully, and the exact queries and returned summaries are in searches.jsonl and the item's mathlib_searches. I read the actual candidates in Etale/Locus.lean:103 and DedekindDomain/Dvr.lean:128-137. The former only spreads etaleness; the latter assumes a Dedekind domain and a nonzero prime and gives a prime localization. Neither supplies the desired principal DVR neighbourhood. No unavailable service was represented as a negative result.

## Not duplicates

No new nodes; there are no new/existing pairs to compare.

## Review by Q81

I checked the item against Models Tag 0CDD, third proof paragraph, where the affine etale base is shrunk by prime avoidance. I also read the relevant local statements in More on Algebra (lemma-dimension-etale-extension, Tag 07QP; lemma-regular-etale-extension; lemma-Dedekind-etale-extension, Tag 0AP2) and Algebra Tag 00PD, lemma-characterize-dvr. The adopted proof is marked by agent: its explicit finite-spectrum and fraction arguments expand the source's short shrinking sentence. It preserves the inherited nodal-model application of the alteration route and uses no SGA source.

1. Step 1 cites def-sc-discrete-valuation-ring, whose statement really gives a local PID domain which is not a field. The written divisibility/cancellation argument proves every nonzero prime maximal; localness then identifies it with m_R. It needs neither a separate dimension theorem nor an unstated factoriality theorem.
2. Step 2 uses the actual affine fibre-product formula of lem-weil-pbc-fibre-product-affine-spectra, quasi-compactness from lem-weil-pbc-affine-scheme-qcqs, and discreteness of the fibres from lem-weil-pbc-etale-fibre-discrete-separable-points. I read Schemes lemma-fibre-product-affine-schemes (Tag 01I4), Algebra lemma-quasi-compact (Tag 00E8), and Morphisms lemma-etale-over-field (Tag 02GL). The statement of def-pc-scheme-fibre includes the homeomorphism onto the set-theoretic fibre, so the final finite-union inference has the needed identification, not merely a definition of a fibre product. The singleton finite-subcover argument is elementary. Both generic and closed fibres are used; an empty generic-only component is not silently discarded.
3. Step 3 uses no outside theorem. It chooses one element in p minus q for each of the finitely many primes p not contained in q, and takes their product. Primality of q proves that the product avoids q; its chosen factors prove that it removes every unwanted prime. Every prime below q survives. This is the finite prime-avoidance step itself, not a new node or an uncited appeal to a general avoidance theorem. The empty product is explicitly 1.
4. Step 4 uses exactly clause (1) of lem-weil-pbc-localization-prime-residue-field-iso, which gives extension/contraction and the bijection of primes for a multiplicative localization, and lem-weil-pbc-proper-ideal-contained-in-maximal. I read Algebra lemma-spec-localization (Tag 00E3) and the cited maximal-ideal assertion in lemma-Zariski-topology (Tag 00E0). The surviving primes all lie under q, and extension preserves their containment. Existence of maximal ideals then makes qC the unique maximal ideal. I corrected an initially inaccurate source-tag draft for the maximal-ideal assertion to the actual 00E0 label before delivery.
5. Step 5 uses the local unit criterion only after C has been proved local. It uses the actual fraction/zero criteria of def-weil-pbc-localization-at-prime and def-weil-ring-localization-away, and the same prime correspondence for contraction. The explicit surjectivity and kernel calculations show C is the prime localization as a B-algebra, with the same maximal ideal. They do not assume B is a domain, do not invert elements of q, and do not rely on an unproved assertion that a local ring is already the stalk.
6. Step 6 uses the full statement of lem-sbc-etale-trait-stalk: at a point above m_R the actual stalk is a domain DVR and its canonical structural map is injective. The hypotheses in that statement are exactly available: R is a domain DVR, X to Spec R is etale, q lies over m_R, and a uniformizer exists by the DVR definition. The actual-germ isomorphism in lem-weil-pbc-affine-open-stalk-localization, clause (c), identifies B_q with that stalk and respects every B element, hence the R map. I read Schemes lemma-spec-sheaves (Tag 01HV), especially (1) and (6). Thus transferring injectivity uses an isomorphism commuting with the structural homomorphism. The inverse-image calculation for localness uses localization prime contraction followed by the given contraction q to m_R. It adds no hypothesis to either ring.
7. Step 7 cites lem-weil-pbc-principal-localization-open-immersion, which states a scheme open immersion, not merely a homeomorphism, and clauses (1) and (2) of lem-weil-pbc-etale-composition-cancellation. I read Schemes lemma-standard-open-affine (Tag 01I3) and Morphisms lemma-composition-etale (Tag 02GN); the open-immersion result is Tag 02GP. This proves etaleness for the actual composite Spec C to Spec R. No finite-map assumption is used.

For the B1-B10 and C1-C8 checks, the absence of new nodes eliminates statement-only/definition/duplicate pitfalls; all the real generic facts above have existing statement nodes. The 17 quotations in citations.json were checked as exact substrings of those statements. The source's hidden shrinking argument is now in steps 1-5 rather than relabelled into a new node (D1-D5). Each proof step is shorter than 800 characters, and none hides a separate non-elementary comparison. In step 5 the comparison is the explicitly verified elementary fraction calculation. The two off-unit non-Mathlib/nonclosed tools, lem-sbc-etale-trait-stalk and lem-weil-pbc-localization-prime-residue-field-iso, are declared under split_report.tool_uses, with the generic local-algebra purposes stated there; no maintainer-owned tool_uses field is set.

I tested the mathematical edge cases (E1-E7): B=R gives b=1 and the original DVR; B=0 admits no q and is not mistakenly treated as a DVR; a disconnected algebra R times Frac(R) has its generic field factor removed by the selected element; finite etale algebras over a nonhenselian DVR can have several closed primes, and the product removes the other primes without assuming B finite after shrinking; the proof does not assume B connected, normal, or a domain. The special-fibre condition is used exactly at the stalk theorem and local-map conclusion. Dropping it would allow the explicit field counterexample above.

The server review_split check passed on the seven-step split. The full deliver.py --no-push dry run also exited successfully and printed OK (not pushed), with preflight passed, at 7ed8fa91e50. This includes the server DAG and split checks. A final dry run checks this completed report before the authorized direct push.

## What could not be finished

Nothing mathematical remains for this stage-1 split. No Lean was written, no compiler or Lake/build tool was run, and no repository or launcher file was edited.
