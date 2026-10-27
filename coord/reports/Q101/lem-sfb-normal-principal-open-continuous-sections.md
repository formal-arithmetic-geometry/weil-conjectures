# Stage-1 report: lem-sfb-normal-principal-open-continuous-sections

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-principal-open-continuous-sections.json: statement, split; no exact Mathlib match for the whole item. Six proof steps, all using existing nodes. Statement and statement dependencies retained.
- citations.json: twelve verbatim statement quotations covering every proof citation.
- searches.jsonl: actual msearch.py results, including the completed search recovered after the provider interruption.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and normal/principal-open/continuous-function notions found no project declaration covering all clauses. Existing normal-total-fraction and clopen/component declarations cover only tools. No Lean file was written and no compiler, Lake or build tool was run.

## Literature wanted

None.

## Findings and changes

The original statement is valid as written. Normal does not mean domain here: the proof uses normality at every prime and the total ring of fractions, not a fraction field of Q. The existing normal-integral-closure node explicitly covers rings with arbitrarily many minimal primes. The alternative node lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions needs finitely many minimal primes and was deliberately not used.

The original item had no proof. The argument now proves the idempotent and clopen clauses directly, then assembles existing component and ultrametric theorems. It cites normalized continuous-comparison coherence so that the coefficient conclusion concerns actual restriction and evaluation on the ambient site's objects. No clause was replaced by a newly named copy of itself.

The current unit's direct-images paragraph (3) is the inherited route. Its current source is literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. The unit record is an older sec-six-functors record, whereas this item's inherited chapter is sec-six-functors-basics. The nearest ancestor tool prints None, agreeing with the item's existing null blueprint.from.node; the existing source anchor is retained. No unit or chapter record is changed because this item is not the unit's key statement.

## Review by Q101

I read Stacks algebra.tex Tag 034M, lemma-normal-ring-integrally-closed, including the local-denominator proof, and Tag 00EE, lemma-disjoint-decomposition, including uniqueness. I read topology.tex Tag 0906, lemma-spectral-pi0, and opened the full statement and dependencies of lem-sfb-spectral-clopen-component-homeomorphism. For coefficients I read Hemo–Richarz–Scholbach Example 3.1 on PDF page 6, which explicitly identifies the sheaf with U mapped to continuous maps from its underlying topology, and the surrounding scheme-pullback discussion; Bhatt–Scholze Lemma 4.2.12 supplies the continuous-function sheaf and component viewpoint. I opened all twelve cited node statements, not just their titles or proofs. No new nodes have sources to audit.

Step 1 uses the explicit fraction relations in def-weil-ring-localization-away and def-weil-pbc-module-localization, the monic-polynomial definition in def-weil-pbc-integral-closure, and exactly the conclusion of lem-weil-pbc-normal-ring-integrally-closed-total. The powers of s remain regular, so Q embeds into Q[1/s] and into its total fractions, even without the domain or Noetherian hypothesis. A numerator killed after inclusion in total fractions is killed by a regular denominator and hence is zero. Every localized idempotent satisfies the monic equation t^2-t=0; the cited normal-ring statement supplies its preimage in Q. Injectivity proves this preimage is idempotent and unique. This is the actual algebraic argument, not a new assertion of idempotent invariance passed to another node.

Step 2 uses precisely the bijection of idempotents and clopens in lem-weil-pbc-spec-clopen-idempotent. The preimage formula is written out using membership in a contracted prime ideal. I also read Mathlib/RingTheory/Spectrum/Prime/Topology.lean lines 1078–1089 (the idempotent correspondence) and 615–617 (the definitional basic-open preimage equation), the relevant LeanFinder hits. The localization hits in Away/Basic.lean concern localization at an idempotent, not idempotent invariance under localization at an arbitrary regular element, so they do not finish the item.

Step 3 explicitly gets qcqs from lem-weil-pbc-affine-scheme-qcqs and spectrality from lem-weil-pbc-qcqs-scheme-spectral before invoking the spectral clopen criterion. The latter states both the homeomorphism and its required normalization for the quotient topology. It assumes continuity, which the given principal open immersion has. I did not replace the component quotient by the set of irreducible components or assume components open.

Step 4 invokes lem-sfb-ultrametric-component-map-extension with exactly its spaces, continuous map, homeomorphism, field, and ultrametric hypotheses. Its statement supplies total disconnectedness, the unique continuous factorization, the ring isomorphism for actual precomposition, and the explicit inverse. In particular it requires neither completeness nor local compactness of E; its empty-space and trivial-valuation clauses cover those boundary cases.

Step 5 checks the hypothesis of lem-weil-pbc-condensed-field-continuous-realization using the total disconnectedness from step 4. That node states a ring-sheaf isomorphism on any scheme, not just Noetherian schemes or finite extensions. The def-sfb-continuous-ring-canonical-comparison statement spells out the same profinite-test adjunct normalization. The scheme-pullback equation of lem-sfb-normalized-continuous-set-comparison-coherence identifies the actual coefficient comparison with precomposition; its assumed comparisons and sheaf property are provided here by the canonical ring-sheaf realization. Thus the proof does not infer arbitrary-morphism naturality merely from existence of isomorphisms. Evaluating the sheaf on X and X_s in Z_proet gives the claimed ambient-site evaluation directly; no assertion that all pro-etale objects are normal is made. Normality and regularity are hypotheses only of the pair under consideration.

Step 6 is elementary: the commuting square gives equality of precompositions, and injectivity already proved for the source pair identifies the two candidate extensions. This also proves naturality of the inverse, rather than simply calling it transport. The zero ring has empty spectra and a unique function to E; all section rings are the zero ring. At s=1 restriction and its inverse are identities. Finite products of normal domains satisfy the argument componentwise, and infinite products need no additional minimal-prime assumption: the argument never enumerates minimal primes. The regularity hypothesis is essential (e.g. Q=k times k and s=(1,0) would discard a component); no such nonregular example is admitted.

Against delivery-errors B–E: every object and notion remains introduced in the item's statement; all substantive facts have existing cited nodes with exact statement quotations; no new nodes, hidden proof sketches in new statements, unsupported tags, circular dependencies or off-route replacements were introduced. I checked that none of the cited proof-dependency closures returns to this item. Every step is shorter than 2000 characters. The two off-unit non-Mathlib tools are declared in split_report.tool_uses: the generic total-fraction integral-closure theorem and the generic continuous-coefficient realization. The other non-Mathlib tools are in the item's own unit; affine qcqs, spectrality, fraction definitions and clopen correspondence are Mathlib leaves.

## Mathlib and blueprint search assessment

The recorded fresh semantic searches used two different formulations, extension of continuous functions and invariance of idempotents under regular localization. I read the returned names. They lead to the existing clopen-idempotent correspondence, general structure-sheaf statements, domain-only integral-closure/localization theorems, or unrelated C-star continuous functional calculus. Loogle for ContinuousMap together with PrimeSpectrum has no hits. The regex search returns the definitional basic-open preimage equation and unrelated convenient-topology localization, not this theorem. Searches of the whole DAG found the stronger reusable generic tools cited above, and blueprint_refs.py searches for connected components, continuous maps, and principal opens found no blueprint node stating this item exactly. blueprint.same_as remains empty.

## Unfinished work

None in this stage-1 split. Existing unsplit tool nodes stay in the DAG queue; in particular this item cites the stated ultrametric-component extension theorem without splitting or changing that independently owned item. Maintainer independent review remains the normal delivery review.
