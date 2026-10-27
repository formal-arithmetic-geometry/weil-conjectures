# Stage-1 delivery: lem-sfb-local-domain-same-field-dvr

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-same-field-dvr.json`: item, statement unchanged, five proof steps, status split; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-local-domain-birational-dimension-one.json`: one new statement-only node, unsplit; no exact Mathlib match. It asserts the birational dimension-one local overring of Stacks 00P8, without the unused essentially-finite-type clause.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `searches.jsonl`: actual search-command records; original searches in the item's repository record retained, new searches appended honestly.

One new node; zero new Mathlib leaves. The new node has empty proof and proof_deps and null proof_origin. Its notions are either inline (domain, local, fraction field, contraction) or cited definition nodes. No Lean or library files, repository files, launcher files, or coordination records were written.

## Attachments

None. I searched the live WeilConjectures source by the blueprint id and the domination/fraction-field notions. `IsLocalRing.exists_isDiscreteValuationRing` in `WeilConjectures/RingTheory/DiscreteValuationRing/Dominating.lean:250` has a proof without sorry, but its statement concludes only an injective local map to some DVR. It does not identify that DVR's fraction field with the input's field, so it cannot attach this item. Similarly `IsLocalRing.exists_ringKrullDim_eq_one` at line 182 omits the birational containment and prescribed fraction field required by the new node. Its proof constructs them internally, but a proof's internal witnesses are not a public statement (C3). The useful one-dimensional valuation-discreteness theorem at line 126 does not supply the needed dimension-one birational overring.

## WANTED

None. All sources used are available locally in literature/stacks-project/algebra.tex.

## Problems found and changes

The item is true as stated and needed no statement repair. It was an unsplit statement-only node, rather than a proof. I followed its source 00PH for L = K, retaining the fraction-field and local-map requirements explicitly throughout. The single new node isolates the genuinely smaller 00P8 reduction: it produces a possibly nonnormal one-dimensional Noetherian local domain, without asserting any DVR. The item's proof then performs the integral closure, chooses its prime, proves it is a nonzero maximal ideal using an existing theorem, localizes, and checks the contraction.

The current ancestor command prints blueprint.from.node = None for this item. I retained that inherited null blueprint anchor and extended its exact existing place and via chain; the new node follows the command's same anchor. Whole-blueprint searches for dominating/dominate, DVR, one-dimensional, dimension 1, same fraction field, 00P8, Krull-Akizuki and blowing up found no equivalent statement. The unit and chapter records were read; this is a generic commutative-algebra prerequisite on the existing boundary-point route, with no alteration of a unit step.

## Not duplicates

lem-sfb-local-domain-birational-dimension-one vs lemma-nagata-local-domain-valuation-dominates: that existing node supplies a valuation ring, with no Noetherian or dimension-one assertion; 00P8 supplies a Noetherian local dimension-one overring, with no assertion it is a valuation ring.
lem-sfb-local-domain-birational-dimension-one vs lem-sfb-local-domain-same-field-dvr: the new node does not assert normality, principality of ideals, or a DVR; normalization and localization in the item are still necessary.
lem-sfb-local-domain-birational-dimension-one vs lem-sc-integral-closure-dedekind-surjective-fibres: that node assumes the starting domain already has dimension one and normalizes it; the new node starts in arbitrary dimension and supplies the local dimension-one overring.
lem-sfb-local-domain-birational-dimension-one vs lem-sc-normal-dim1-dvr: that node assumes normality and dimension one and concludes DVR; the new node supplies dimension one from an arbitrary nonfield Noetherian local domain and gives no normality.
No existing DAG node shared Tag 00P8 or label algebra-lemma-dominate-by-dimension-1 in the searches before creation. The same-tag duplicate gate therefore has no required pairs.

## Review by NQ

I read the statement and full proof of algebra-lemma-exists-dvr (Tag 00PH), including its reduction and normalization paragraphs, and algebra-lemma-dominate-by-dimension-1 (Tag 00P8), including its valuation/affine-blowup/principal-height proof. For the one new node, 00P8's inclusions and first two clauses give precisely the asserted R and contraction. The extra fraction-field sentence is elementary: B is contained in R contained in K and every element of K is already b/c from B. I deliberately did not export the essentially-finite-type clause or repeat the whole DVR conclusion. I also read the source statements and proofs of 09IG and 031F and the Dedekind-localization statement 034X; the selected existing normal-localization node states exactly the embedding and fraction-field identification used here.

For step 1 I opened the new node's complete statement and checked its hypotheses against the item: nonzero local domain, Noetherian, nonzero maximal ideal, and the specified fraction field. It supplies the actual subring R in that K, dimension one and the contraction, so nothing is borrowed from the proof of the weaker project existence lemma.

For step 2 I opened def-weil-pbc-integral-closure and lem-sc-integral-closure-dedekind-surjective-fibres. The former defines C as a subring containing R. The latter explicitly supplies a Noetherian integrally closed domain of dimension one and surjectivity on spectra; its finite-extension hypothesis is satisfied by K/K of degree one. Surjectivity gives exactly a prime q contracting to m_R. The ratio argument written in the step proves Frac(C) = K and is not inferred from the word normalization alone.

For step 3 I opened lem-weil-pbc-dim-one-residue-field-extensions-finite. Clause (1) says every prime over the maximal ideal of the Noetherian local dimension-one source is maximal, under a finite fraction-field extension. I checked R, C, K/K and the contraction separately. The step also witnesses q nonzero using a nonzero element of m_B. In the draft I initially considered a prime-chain argument for maximality; I replaced it by this exact existing node to avoid concealing a dimension-zero-domain argument. No new node was needed.

For step 4 I opened def-weil-pbc-localization-at-prime, lem-weil-pbc-localization-normal-domain, and lem-sc-dedekind-localization-dvr. The normal-localization node explicitly gives the injection into the same fraction field, not just normality. Its hypotheses hold since C is integrally closed by step 2 and 0 is in q, hence outside its complement. The DVR node explicitly applies to a Noetherian integrally closed dimension-one domain at a maximal ideal. Step 3 supplies maximality and nonzeroness, so the field-localization edge case is excluded. The pinned Mathlib declaration at DedekindDomain/Dvr.lean:128 has exactly this nonzero-prime requirement, and its source was read.

For step 5 I reopened the localization definition: it states the maximal ideal is qC_q. The argument c in q maps into that ideal, while c outside q maps to a unit with explicit inverse 1/c, proves its contraction without assuming an unstated comparison. Iterating the contractions gives m_A intersect B = m_B. This is the only elementary proof step; it is the two-line unit calculation plus substitution of already proved equalities. All non-elementary steps cite statements that actually give their claimed conclusion. Every citation is copied verbatim in citations.json.

I checked small cases for both the item and the new statement: a DVR (take R=B, and C=A=B), the singular one-dimensional local domain k[t^2,t^3]_(t^2,t^3) (the dimension-one overring can already be B; normalization gives k[t]_(t)), and the two-dimensional ring k[x,y]_(x,y) (the affine chart with y/x, localized at the prime (x), gives a dimension-one local overring with the same field and contraction). These cases distinguish the new reduction from the final DVR assertion. A field is rightly excluded: a DVR A contained in K and containing B=K would force A=K. No excellence, normality, residue-field finiteness or completeness was assumed of B. No statement-dispute or source error was found.

I read delivery-errors B through E in full and checked their issues in the actual files: self-contained statements, definitions, exact source tags/labels, no unsplit proof, no duplication or clause restatement, actual logged searches with second phrasings, no proof-as-statement citations, no missing non-elementary fact and no cyclic route. The two off-unit algebra statements are declared generic tool uses in split_report for review. Every proof step is shorter than 2000 characters. No forbidden SGA source appears.

Mathlib searches used the required command for LeanSearch, LeanFinder, Loogle and grep and were read, with a second concept phrasing for each negative conclusion. The results classify existing local/valuation rings or localize given rings and primes; they do not supply the birational dimension-one overring or the same-field DVR in this generality. All queries recorded for the new node occur in searches.jsonl. The original item's inherited search records were retained, not invented or replayed as new runs.

## Unfinished work

The new 00P8 node is intentionally statement-only and joins the stage-1 queue. No part of the item's proof is left as a sketch. Server dry run and direct delivery follow this report.
