# Q108: lem-sf-adic-proper-adjunction-realization

## Files written

- dag/nodes/sec-six-functors/lem-sf-adic-proper-adjunction-realization.json: statement, now split in eight steps; no exact Mathlib match. Statement and statement dependencies unchanged.
- citations.json: one verbatim statement excerpt for every step/node citation.
- report.md: this report. searches.jsonl is the search tool's unmodified log. write_split.py is sandbox-only preparation code.

There are **0 new nodes and 0 Mathlib leaves**. All 24 distinct proof dependencies already exist in the live DAG. No Lean, compiler, Lake, repository write or direct git command was used.

## Attachments

None. The project Lean search for the exact id/docstring and for adic realization/adjunction found no declaration of this full statement. Existing AdicRealization and finite-coefficient projection-formula modules concern other coefficient constructions and do not state this ordinary continuous-Omega comparison with every clause. The item has lean_audit none/none. Sorry declarations were not treated as completed proofs.

## WANTED

None. The source needed for the item is present.

## Findings and corrections

The imported item had a statement and no proof. I kept its statement, including the actual ordinary module derived categories, finite-subextension-valued coefficient convention, balanced pullback comparison, and exact counit equation. I did not substitute discrete constant coefficients or a category of Frobenius pairs. The existing source note correctly warns that Proposition 6.8.14 does not state the entire normalized adjunction comparison verbatim. The proof_origin is therefore agent, assembling existing statements rather than attributing its mate equations directly to Bhatt–Scholze.

The previous source route had no blueprint ancestor: blueprint_refs.py ancestor returned None. I kept the existing from.node=null and its recorded chain through the compact projection formula and Verdier exchange. The relevant main-20261015 blueprint file is sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md, Step 1, second Hom bijection. This split supplies the proper adjunction normalization needed by its parent; it does not use a projection formula to prove that normalization. Searches of the whole imported blueprint for continuous coefficient, rational realization and proper adjunction produced no same statement. The last search returned cor-exc-base-change-reduces-to-proper, which is a reduction theorem and does not state the realization comparison.

I reused the already-reviewed lem-sf-locally-finite-adic-compact-support-realization at the compactification (id,p) solely to prove that actual ordinary Rp_* preserves the desired subcategory. I did not assume its displayed comparison is automatically our adjunction mate. The latter is constructed independently and proved invertible by the existing abstract mate-isomorphism theorem. This removes any need to add a new node for either clause of this item.

The Mathlib searches were genuinely run through msearch.py: LeanSearch, Loogle, grep and two LeanFinder phrasings. All services returned results. I read the logged hits, the sheaf pullbackPushforwardAdjunction declaration at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:60 and the ElladicCohomology definitions (ellAdicSheaf at line 63). These give underived adjunctions or a continuous integral coefficient sheaf, not the geometric constructible adic realization theorem. The second LeanFinder phrasing returned general condensed/derived functor identities, again no such comparison. The inherited searches were retained and the new exact queries appended from the genuine log.

## Unfinished work

None in this one-level split. The existing cited lemmas remain responsible for their own proofs; none is copied into a new node. No unit realization field needs changing: this is not the unit's key statement.

## Not duplicates

No new node was created. The existing compact-support realization proves preservation and a proper comparison but does not assert that the balanced pullback comparison and its right mate identify the actual units and counits. The existing finite-field ordinary adjunction comparisons do not alone cover the common-finite-field Omega realization. Those existing results are cited rather than duplicated.

## Review by Q108

I read Bhatt–Scholze, pp. 60–62, including the constructibility definitions, Proposition 6.8.14 and all of Remark 6.8.15, and the pushforward/adjunction assertion of Lemma 6.7.2 on p. 55. These identify the relevant ordinary continuous module operations and explain why their constructible restrictions, rather than discrete coefficients, are the right ones. There are no new nodes needing a separate source review. I read the chapter and the biduality unit; their routes are not changed. The generic off-unit geometric, completion and mate results are declared in split_report.tool_uses with their purpose.

For Step 1 I opened all five cited statements. The finite-type Noetherian and dimension results give the actual hypotheses of the finite-E realization. A field is Noetherian and ell is invertible over k. The coefficient-ring realization explicitly intertwines scheme maps with precomposition; the two realization lemmas give the same scalar-extension object and the same fractional/common-stage morphisms. Thus the identification of rho and J uses their stated formulas and not an unnoticed equivalence of discrete and continuous sheaves.

For Step 2 I read the pullback-comparison statement, especially its inverse of the specified completion unit and its warning that naive inverse image of the coefficient sheaf need not be the new coefficient sheaf. I use the balanced module pullback throughout. The scalar-coherence statement supplies the precise finite-field square, including ramification and the normalized comparisons. The general ringed composition theorem handles the final extension to B. Their hypotheses are available from Step 1. Equality of common-stage arrows is checked after a common finite extension, exactly as the existing category definition prescribes. The realization equivalence then gives preservation of the full target subcategory.

For Step 3 I read the exact specified-map clauses of ordinary/completed pullback and constructible tensor completion. Both use actual quotient maps. The cochain tensor comparison states equality of chain maps commuting with transitions, and the primitive-counit comparison states functorial identifications of the entire systems and naturality before evaluation. Consequently Step 3 applies a functor to equal whole-diagram maps and substitutes invertible comparisons; it never treats individual reduction functors as faithful. This short diagram argument does not hide a separate geometric theorem. For Step 4 the ringed monoidal comparison theorem states its monoidal and unit equations, and rho is explicitly symmetric strong monoidal. Scalar multiplication has degree zero, so the signed tensor formula retains its sign. The common-stage operation definition says how arrows are represented, completing descent of this equation.

For Step 5 I opened the compact-support realization statement and its recent independent review. It explicitly says actual F^c preserves the indicated category and allows the compactification (id,p) for proper p. Extension by zero along the identity is the identity directly from its definition. The finite-Tor definition explicitly equates the field-stage ctf and bounded constructible categories: no unjustified integral or finite-ring Tor hypothesis is used. Hence actual Rp_{*,B}, not an abstractly selected right adjoint, restricts as required.

For Step 6 I read the common-stage ordinary adjunction, finite-field direct-image realization, finite-scalar adjunction compatibility, the full common-stage coefficient definition, and the ambient ringed derived adjunction. The common-stage definition explicitly identifies the pair-category convention used by the ordinary adjunction theorem. The finite-field realization explicitly identifies actual units and counits, while the scalar compatibility asserts the actual comparisons are mates. This pins down the adjunction used in Step 7; a definition of direct image alone would not have supplied that theorem. Restriction is legitimate because the subcategories are full and both functors preserve them, so their Hom bijections and unit/counit maps are unchanged.

For Step 7 I opened the mate definition and the mate-isomorphism theorem. The orientation is alpha=a_p inverse, L'G to HL; the displayed b formula has source rho_Y Rp_* K and target Rp_{*,B} rho_Z K. Both realization functors are equivalences onto the full constructible subcategories, satisfying the theorem's equivalence/fully-faithful hypotheses. Step 8 cites the two explicit categorical counit and unit identities, substitutes that same alpha, and cancels a_p inverse on the correct side. These identities give precisely the item's displayed equation, including its order of composition, and its unit analogue.

I checked B–E of delivery-errors.md against these files. There are no statement-only children, hence no new-node self-containment, tag collision or Mathlib-leaf issue. Every non-elementary input in the proof is cited, every cited statement was opened, and citations.json uses its literal text (including line breaks where present). No cited dependency has a path back to the item in the read DAG. I checked the longest step (1257 characters); no step exceeds 2000 characters. There is no statement dispute or change to report.

Small cases: for p=id, coefficient precomposition and balanced multiplication give the identity comparisons and the identity adjunction equations; for empty schemes or zero complexes all relevant maps are the unique zero-object maps; the identity isomorphism between equal coefficient fields inserts and removes 1. For ramified E subset L the cited scalar-coherence statement explicitly allows arbitrary ramification. For a nontrivial proper map, such as P^1_k to Spec k, no cohomological vanishing or equality of coefficient inverse images is assumed: preservation is supplied by the compact-support theorem, and the unit/counit statements are ordinary derived identities on all bounded constructible inputs.

## Repair of the landing refusal (2026-10-22)

The return was a landing-time dependency change, not a rejected mathematical split: `lem-sf-locally-finite-coefficient-ring-realization` had changed since the reviewed delivery. I retained the delivered eight-step proof and search log, compared its payload with the current repository item (still unsplit), and found no change to the item's statement or statement dependencies. The required initial dry run rebased that retained payload through deliver.py onto the current server DAG and passed at `442311b6399`; I then repaired the citation explicitly rather than re-pushing that unchanged payload.

Under my Review by Q108 signature, I reread the full current statements of all 24 proof dependencies, including the changed coefficient-ring statement and its maintainer review. That review records the newly explicit references for the continuous finite-field realization and the coefficient-map mate. The statement continues to give a canonical ring-sheaf isomorphism for arbitrary schemes, with no new Noetherianity or separatedness assumption. Its finite-field clause uses the condensed ring of continuous E-valued functions; its scheme-map clause names eta_h as the mate of the canonical coefficient pullback comparison. These are exactly the normalizations Step 1 needs.

I replaced Step 1's short naturality assertion by the actual square `(p_* theta_Z) eta_p = beta_p theta_Y`, and took its adjoint to identify the structural ring map for balanced module pullback. The finite-E inclusion is separately identified with postcomposition. This makes explicit why the current citation supplies both facts without assuming that naive inverse image of the coefficient sheaf is an isomorphism. I replaced the old 46-character citation fragment with the complete canonical-isomorphism, finite-field-inclusion and scheme-map paragraphs copied verbatim from the current dependency. No cited node was edited.

For the remaining steps I revalidated their inputs against their current statements: Step 2 has the specified inverse completion unit and finite-field coherence square; Step 3 has whole-system chain-map and primitive-comparison naturality, not just separate reductions; Step 4 has the monoidal composition equations and common-stage tensor definition; Step 5 has actual direct-image preservation at compactification (id,p) and the field-stage finite-Tor equality; Step 6 has the actual finite-field adjunction normalization and scalar mate identities; Step 7 has equivalence/fully-faithfulness hypotheses for mate invertibility; Step 8 has exactly the two mate unit/counit identities with the displayed orientation. All 28 step/dependency citation pairs remain supported by literal statement excerpts. No other citation needed replacement.

I reread the local Bhatt–Scholze Proposition 6.8.14 and Remark 6.8.15 (pp. 61–62), and Hemo–Richarz–Scholbach Example 3.1 (p. 6), the source used by the changed coefficient node. The coefficient node itself supplies the locally finite/finite-subextension identification; I do not infer it for all norm-continuous Omega-valued functions from the source. The original route, source qualifications, edge-case review and genuine Mathlib searches above remain applicable. In particular, for p=id the square becomes the identity square; zero objects and empty schemes retain their unique maps; finite-E inclusion remains continuous, including ramified extensions. All proof steps remain below 2000 characters. There are still zero new nodes and zero Mathlib leaves, and the item's statement and both dependency lists are unchanged.

## Validation

The server review_split check passed. The first delivery dry run rejected citation excerpts shorter than its 40-character minimum; I replaced the fragments with substantive verbatim sentences/formulas, retaining the split unchanged.

The next preflight flagged the phrase “the item's” in Step 5 under its standalone-text rule. I replaced it with the explicit category C_Z; the mathematical assertion and all citations are unchanged.
