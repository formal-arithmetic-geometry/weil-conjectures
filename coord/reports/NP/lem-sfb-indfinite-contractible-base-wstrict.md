# Stage-1 report: lem-sfb-indfinite-contractible-base-wstrict

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-indfinite-contractible-base-wstrict.json: item, split in eight steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-filtered-colimit-strictly-henselian-local.json: new statement-only unsplit node, Stacks 04GI; no Mathlib match.
- citations.json: verbatim statement quotations for every step-node citation.

## Attachments

None. I searched the current WeilConjectures source for the blueprint tag and for wStrict, WStrict, w-contractible and indfinite. IsWContractibleRing.of_finite in RingTheory/ProEtale/FiniteWContractible.lean proves the finite-stage result only; IsWStrictlyLocalRing.of_finite similarly treats a single module-finite algebra. Neither states the directed-colimit result with its two homeomorphisms. The existing finite-stage DAG node is reused. The local-colimit searches of the project's RingTheory source gave henselian-pair constructions, not the strictly henselian local permanence statement.

## WANTED

None. All mathematical sources used are present in literature/.

## Problems corrected or retained

The imported item statement is correct and unchanged. Its source's Example 2.2.2 says “cofiltered limit of ... rings”; I use the geometric meaning specified by the item, namely a cofiltered limit of affine spectra and a filtered colimit of coordinate rings. This is a clarification of the proof, not a changed hypothesis or conclusion. I did not infer w-contractibility of the limit.

The original blueprint ancestry has from.node=null. The required blueprint_refs.py ancestor command confirms None. I retained that value and the inherited paragraph (3) location and via chain, and recorded the actual source places. No unit or chapter file is edited. Searches of the whole imported blueprint for w-local, henselian, colimit-henselian, 04GI, strictly henselian local rings, henselian colimit and local homomorphisms found no duplicate of the new theorem. A broad limit search was also inspected. The new node follows this item's recorded root-tower coordinate-face subargument and does not alter its route.

## Not duplicates

lem-sfb-filtered-colimit-strictly-henselian-local vs lem-wf-strict-henselization-finite-lifts: the latter constructs a particular diagram of finite local etale algebras over a henselization and identifies its colimit with a chosen strict henselization. It does not give permanence for arbitrary strictly henselian local rings and arbitrary local transition maps.

lem-sfb-filtered-colimit-strictly-henselian-local vs lem-trf-integral-component-henselian-permanence: the latter concerns an integral algebra over one henselian local base with no nontrivial idempotents; it imposes integrality and connectedness, not a filtered diagram of local homomorphisms.

lem-sfb-filtered-colimit-strictly-henselian-local vs lem-weil-pbc-strict-henselization-triples: the latter constructs a pointed etale-neighbourhood colimit over a fixed ring, prime and separable closure. It does not state the arbitrary local-ring colimit theorem. These are all existing DAG nodes returned by the 04GI/lemma-colimit-henselian search.

lem-sfb-filtered-colimit-strictly-henselian-local vs lem-weil-pbc-filtered-colimit-henselian-pair: the latter proves permanence of henselian pairs, including their colimit ideal; it asserts neither that the colimit is local nor that its residue field is separably closed. Recovering the present theorem from it still requires both additional facts.

## Review by NP

I read Bhatt–Scholze §2.1, specifically Definition 2.1.1, Lemma 2.1.4, Remark 2.1.5, and Lemma 2.1.9 with its proof, followed by Definition 2.2.1 and Example 2.2.2. I read Stacks proetale.tex lemma-finite-finitely-presented-over-w-contractible, Tag 0986, statement and proof, and algebra.tex lemma-colimit-henselian, Tag 04GI, statement and proof. The latter is the source for the only new node, including its local-homomorphism hypothesis. Its proof descends a polynomial and a simple residue root to a stage; it also explains locality and the residue-field colimit. I leave this genuine algebra theorem unsplit, rather than hiding it in the item's local-ring step.

Step 1 uses the complete statement of lem-ce-finite-finitely-presented-wcontractible, whose module-finite and algebra-finitely-presented hypotheses are exactly available. It gives all three geometric properties, including the two needed here. I checked det-pe-wlocal-components clause 3 explicitly equates the two conventions used by that theorem and this item. sk-def-pe-wlocal defines strict locality by the maximal localizations, so no converse splitting-of-etale-covers theorem is being smuggled in.

Step 2 uses lem-weil-pbc-finite-algebra-is-integral, whose statement explicitly makes a finite algebra integral, and lem-weil-pbc-integral-maximal-contracts-maximal, which explicitly contracts maximal ideals. The transition map is an A-algebra map, so the original finite A-generators of B_j are also B_i-generators: the coefficient expression is written in the step. This does not require flatness, injectivity or finite presentation of transition maps.

Step 3 uses lem-a1-filtered-spectrum-topological-limit, whose statement provides precisely the compatible prime families and the initial coordinate topology, for a nonempty small directed poset as given. It is not merely the scheme-limit existence theorem. The definition of the affine spectrum gives the Zariski topology; from its basic opens D(b), specialization is inclusion of prime ideals, so in the initial coordinate topology it is coordinatewise inclusion.

Step 4 uses the unique maximal specialization of each finite stage and integral contraction to prove compatibility of their maximal ideals, then the actual compatible-prime-family statement to obtain a prime of B. It checks maximality directly by coordinatewise inclusion and injectivity of the comparison. lem-weil-pbc-proper-ideal-contained-in-maximal explicitly supplies a maximal ideal over any proper ideal, so ruling out a larger prime suffices. No existence of a nonempty inverse limit with surjective maps is assumed: the compatible family is constructed for the particular point.

Step 5 constructs the unique maximal specialization for each point and proves that a maximal point has maximal coordinates, before using the closed-point formula. The formula is an intersection of inverse images of closed subsets of X_i, so proves closedness without assuming projection surjectivity. The restricted comparison is a homeomorphism because the two topologies have the same coordinate subbasis; no general theorem saying closed points commute with limits is cited without a node. These steps are the item's own proof and do not shift its clauses to new nodes.

Step 6 uses exactly clause 2 of det-pe-wlocal-components, which says the closed-point inclusion followed by the component quotient is a homeomorphism. I checked naturality on each closed point: taking its component and applying a spectral map gives the component of its image. Since those images are closed, the finite-stage and limit identifications commute with every transition and projection. This establishes the canonical component comparison, not an unrelated isomorphism of profinite spaces.

Step 7 uses the full statement of lem-weil-pbc-filtered-colimit-localization-at-prime, not a definition of localization: it states the fraction transition maps and the colimit identity at an arbitrary prime. Step 5 supplies that the contracted primes are maximal, and step 1 supplies strict henselianity at each one. Locality of each fraction map is checked by the numerator's membership in the contracted maximal ideal. The new 04GI node therefore applies with every hypothesis verified. sk-def-pe-wlocal now gives the requested ring property.

Step 8 factors the structural closed-point map through any chosen stage. Nonemptiness of D is used exactly here. Its integral contraction assertion is the one proved for A -> B_i in step 2, and the named integral-maximal node states it. Nothing requires B itself to be finite. Zero rings and empty spectra give no points at which to invoke local-ring results; both inverse-limit spaces are empty when appropriate by the spectrum comparison. Finite products of separably closed fields, a single strictly henselian local base, a nonreduced finite algebra, and quotient transition maps all satisfy the argument. Locality in the new lemma excludes the zero local ring, as intended; the item uses that lemma only at an existing maximal ideal.

The new node is self-contained, names its definition and colimit dependencies, has an empty proof and empty proof_deps, and is strictly more general in a different direction than an item clause: it assumes local rings and says nothing about global closed-point spaces or finite algebras. I checked the same-tag DAG results and their statements as documented above. Mathlib searches were run with the required msearch.py command and the exact queries and actual hits are retained in searches.jsonl and the node fields. Two LeanFinder phrasings return HenselianLocalRing, its simple-root characterization, completeness results, fields, and general DirectLimit ring structure, but none gives local strict-henselian colimit permanence. Loogle HenselianLocalRing, DirectLimit and the RingTheory grep give no match; the direct read of Mathlib/RingTheory/Henselian.lean confirms these are definitions and different permanence results. One exploratory grep used a nonexistent directory RingTheory/Henselian; I did not use that entry as evidence or record it in either node. The valid whole-RingTheory and actual Henselian.lean file searches are recorded.

I checked B–E: statements are self-contained, no proof is embedded in the new statement, all substantive facts used by the item are named citations, no use is borrowed from the proof rather than statement of a node, no new node duplicates a clause or existing theorem, and no hypotheses are silently added. All eight steps are below 2000 characters. The off-unit proof tools are explicitly declared in split_report.tool_uses with their algebraic/topological role; no coefficient comparison or alternative six-functor route is introduced. No SGA source is used. citations.json quotes the cited statements verbatim, once for each use.

## Unfinished work

None for this one-level split. The one new algebra node is intentionally unsplit, as required for future stage-1 work.
