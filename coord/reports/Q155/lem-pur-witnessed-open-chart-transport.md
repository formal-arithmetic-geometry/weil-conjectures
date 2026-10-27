# Stage-1 worker report: Q155

## Files written

- dag/nodes/sec-six-functors/lem-pur-witnessed-open-chart-transport.json: existing statement split into eight proof steps; statement and original metadata unchanged; no Mathlib match.
- citations.json: 25 literal statement excerpts, one for every step/node citation. Short excerpts were expanded to the complete statement after the first dry run required at least 40 characters.
- report.md: this report and self-review. searches.jsonl is the search command's original log. write_split.py is sandbox-only scratch work.

No new nodes, no new Mathlib leaves, no unit changes, and no Lean files.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, witnessed/chart names, etaleOrigin, and exceptional/upperShriek notions. Read the finite-coefficient Derived/UpperShriek.lean definitions and domain discussion, its UpperShriekComposition and UpperShriekPreservation declaration listings, and Etale/Derived/UpperShriek.lean's bounded-below interface. Existing transported upper shriek and composition results do not jointly state the item's explicit witnessed open restriction, normalized chart Hom chain, and naturality for every underlying arrow. No declaration is claimed as a finished proof of this item. No compiler or Lake command was run.

## WANTED

None. The blueprint, the retained Q24 proof, Stacks sources and Zheng's paper are available locally.

## Corrections and scope

The sandbox contained only dispatcher markers, so I copied the current repository item. Its statement is unchanged. I reused the complete retained argument in coord/reports/Q24/lem-pur-affine-chart-exceptional-identification.md, returned Steps 1–2 and 6–9. I expanded the second comparison unit and the arbitrary-arrow naturality calculation, rather than leaving these as unspecified transports. I replaced the retained argument's bounded-below citation with the existing coefficient-system adjoint theorem and explicitly extracted its finite-level consequence; the extraction uses only its evaluation comparison and lower-bound assertion and follows the permitted Zheng route. No SGA source is used by this split.

No statement dispute was found. The item is not a key node of its unit; neither the chapter route nor unit records are changed.

## Searches and reuse

Before writing I searched all dag/nodes, including other chapters, by witnessed/etale-origin/chart/compact-support/adjunction/comparison-unit concepts. I read every dependency statement used in the final proof. Whole-blueprint searches used blueprint_refs.py search for open chart, chart adjoint, comparison pullback, open restriction and right adjoint; ancestor confirms thm-pur-general-admissibility. The chapter record and sk-prop-sf-rf-shriek-preservation unit route require the same open-locality and closed/projection argument, which is retained.

Five fresh searches ran through msearch.py: two LeanFinder phrasings, Loogle for CategoryTheory.Adjunction.rightAdjointUniq, grep for witnessed charts/etale chart adjoints/upperShriek, and LeanSearch for the chart restriction isomorphism. Every returned hit was read. Loogle gives generic adjunction uniqueness; the semantic hits give ring-theoretic etale pairs, scheme restriction isomorphisms, and generic derived-category functors. None supplies this item's schemes, comparison functors, D+ hypotheses and witness normalization by a one-line specialization. The grep returned no hits. The inherited six records were preserved, and the five actual new queries were appended from searches.jsonl without editing that log. No service was unavailable.

## Not duplicates

No new nodes were created. The existing lem-sf-etale-chart-adjoint-comparison is reused for exactly its natural bounded-below Hom tests, not treated as already proving the D+ isomorphism or witnessed transport. lem-trf-witnessed-open-pullback assumes separated schemes and only gives the pullback witnesses, so it cannot replace this entire item. lem-pur-etale-witness-transport-data gives a general unit comparison but its explicit witness-naturality clause is for bounded constructible witnesses; here arbitrary D+ witnesses require the full comparison theorem. No extra helper restating a clause of the item is introduced.

## Review by Q155

I read the source thm-pur-general-admissibility.proof.md in main-20261015, particularly Step 1's two chart adjoints and Step 3's source restrictions, the current chapter and unit JSON, and the Q24 retained proof. For comparison I read Stacks proetale.tex lemma-relative-comparison (099V) and lemma-compare-derived (09B1): the first gives the bounded-below unit and the second explicitly handles module coefficients. I also read properties.tex lemma-locally-Noetherian and lemma-Noetherian-topology and categories.tex lemma-yoneda. Zheng's printed pp. 34–37, Constructions 5.14–5.15, the adjoint after Lemma 5.16 and evaluation in Lemma 5.22, support the existing coefficient-system input used here. The proof is marked agent because it develops the agent-written blueprint and its retained Q24 expansion. There are no new-node source claims to audit.

Step 1 uses finite-type-over-Noetherian for X,V and then T, not for a nonexistent separated structure morphism. The affine-space definition gives the actual polynomial ring and structure map; finite generation gives finite type. The open-subscheme node explicitly gives Noetherianity of U. The locally-Noetherian/quasi-separated node supplies precisely the qcqs property used later. All statements were opened, and the field's two-ideal observation is written out.

Step 2 applies the open-subscheme result to each inverse image of an affine open, establishing quasi-compactness of j before using the qc-open finite-type lemma. The closed-immersion-proper statement gives both separatedness and finite type for i. The affine-source-separated statement applies to j, pi and pi i because U,T are affine, irrespective of any property of X over k. The finite-type-composition lemma supplies the composites, and Nagata is applied only after step 1 establishes qcqs targets. Compactifications assumed chosen in the item therefore exist with the stated hypotheses.

Step 3 uses the exactness conclusions of the two constant-module inverse-image theorems, rather than inferring them from the pullback definitions. Exactness computes kernels/images and hence cohomology termwise, so lower bounds and quasi-isomorphisms are preserved. The comparison-pullback statement provides the natural isomorphism and explicitly its identity/composite compatibility. The witnessed-category definition says morphisms are all ambient arrows. These are exactly the facts needed for the lift and the displayed successive-witness formula; no claim about all arrows requires a witness map supplied as input.

Step 4 uses the coefficient-system adjoint statement's actual evaluation isomorphism and lower bound. I checked the strict system used to extract its finite-level consequence: at indices below n it is zero, at n and above the quotient A_m to A_n gives its scalar action, and every transition is linear with the required scalar restriction. Cohomology is levelwise, so a common input lower bound remains a lower bound for the system. Evaluation at n gives precisely H_v at the chosen compactification. This types H_f N_e, H_pi N_e and H_i H_pi N_e before either Q or B is used as a test object. The exact comparison-pullback statement explicitly preserves this lower bound.

Step 5 instantiates the existing chart Hom-test theorem with base open equal to id_V. I checked its factorization fs=vpi and every geometric and coefficient hypothesis against steps 1–2. Its statement, including the displayed i_* and the normalized compact-support compositor, supplies exactly the asserted Hom chain. Its warning that Q and B need not be bounded below in general is respected: that property was proved separately in step 4. This avoids using an unproved ambient right adjoint on pro-etale categories.

Step 6 is elementary evaluation, written out in full: naturality in the test object gives postcomposition by a and b, and the inverse equations for the bijections give both inverse equations for these maps. Evaluation at the identity also proves uniqueness and naturality in N_e. No general Yoneda node restricted to schemes is misapplied to a derived category.

Step 7 uses the comparison theorem's invertible unit at N_e and a second time at H_pi N_e. The latter is D+ by step 4, even without bounded constructibility. The exceptional-image definition supplies exactly C H R, not an ambient pro-etale adjunction. I checked the domains and directions of s_f, s_pi, q_N and t_N: q goes from C_U Q to j* G_f N, while t goes from C_U B to G_i G_pi N. Consequently t (C_U a) q inverse has precisely the requested source and target and carries the specified witnesses. The induced-category definition supplies the inverse arrow as well.

Step 8 uses the full-faithfulness conclusion of the comparison theorem on D+, which includes all module complexes, to recover the unique phi from beta' inverse h beta. The written unit-naturality equation proves naturality of s_v for this arbitrary h. Substitution into q and t, using the already cited pullback comparison and the unit at H_pi phi, proves the two displayed squares. The naturality equation for a then gives naturality of the chart map. Thus no hidden restriction to arrows originally presented as etale morphisms remains.

I tested d=0 (the projection is the identity), identity open immersions, successive identity restrictions, zero input complexes, n=1, and empty U or V. Empty schemes have zero module categories, and the proof takes no maximum or dimension of an empty scheme. No assertion requires constructibility, a common lower bound independent of input, or Tor amplitude. In particular all identities are in the derived categories, not merely per-degree cohomology. All eight steps are below 2000 characters. I checked sections B–E of delivery-errors against the sources and the final JSON: no new-node shape faults, no definition used as an unstated theorem, no new clause-node, and no circular call to this item or its parent. Generic off-unit prerequisites are explained in split_report.tool_uses for maintainer review. The statement, provenance and other maintainer-owned fields were retained.

## What remains

The requested split and self-review are complete. The required server dry run and direct delivery are the remaining operational checks; their final result is reported by the delivery command.
