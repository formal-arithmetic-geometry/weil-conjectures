# Q15: lem-trf-coprime-generators-mprimary-or-unit

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coprime-generators-mprimary-or-unit.json`: statement, split using existing nodes; not a Mathlib leaf.
- `citations.json`: verbatim statement extracts for every citation in all four proof steps.
- `searches.jsonl`: actual msearch results, retained as logged.
- `report.md`: this report.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves.

## Attachments

None. Searched the slopmaster2 project under WeilConjectures for the exact item id, coprime, heightOne/height_one, IsRegularLocalRing, and the RingTheory subtree for radical and dimension-two statements. There is no project declaration giving the item's whole dichotomy. RegularLocalRing/UniqueFactorization.lean proves a different, general UFD fact (with additional framework hypotheses), not this item. Upstream master is reference material only.

## WANTED

None: all sources used are present locally.

## Issues found

The item had no proof. The statement is correct and unchanged. Its source is the Curves proof paragraph at Tag 0C48, lines 3829–3837, not a separate named lemma there. I expanded the inference from absence of a height-one prime to maximal radical, including the otherwise tacit exclusion of the zero ideal. The imported ancestor is lem-trf-local-term-locality; the current main-20261015 ancestor proof discusses contracting correspondences, not this specific algebra lemma. I preserved the actual created.item ancestry and inherited precise descendant provenance rather than inventing a sentence in that ancestor. This item is on the already existing chain through the regular-surface principal-kernel lemma.

The inherited Mathlib searches belong to the creator's Q64 record; I retained them. Six additional searches were actually run with msearch and appended with exactly their query strings. Both natural-language phrasings returned Dedekind/domain or dimension-zero statements, not the item. I read Mathlib/RingTheory/KrullDimension/Zero.lean:108–145: radical_eq_maximalIdeal requires KrullDimLE 0 and cannot be applied to A of dimension 2. I read Ideal/Height.lean:303–324: the height/maximality criterion does not replace the coprime-generator argument. Kaplansky.lean:100–118 gives a useful general UFD criterion but not the requested dichotomy. Loogle returned zero hits. The grep hits for Euclidean domains and Dedekind domains require hypotheses absent here. No search service was unavailable.

## What could not be finished

Nothing in the split remains unfinished. Its existing dependencies retain their own project statuses.

## Not duplicates

No new node was created. Whole-DAG concept searches and blueprint_refs searches for coprime generators, height-one, and radical identified existing inputs rather than a duplicate item. In particular the existing zero-locus/radical node already states the intersection formula; it was reused. The existing UFD/height-one node already states principality and was reused.

## Review by Q15

I read the complete Curves Tag 0C48 statement and proof in curves.tex (3816–3849), checked its label against tags/tags, and read More on Algebra Tag 0AG0 (lemma-regular-local-UFD, 36800–36858), Algebra Tag 0AFT (lemma-characterize-UFD-height-1, 29459 onward), and Tag 00E0 (lemma-Zariski-topology, especially assertion (7)). These are precisely the regular-local UFD, height-one principality and radical-intersection facts used in the proof. There is no SGA citation.

For Step 1 I opened the whole existing regular-local UFD boundary-factorization node and read its statement. It explicitly supplies the integral-domain/UFD conclusion for any regular local ring with a parameter sublist, including r=0. The empty sublist imposes no restriction on A. I do not use its proof or claim it supplies the gcd factorization of a finite list. The nonzero-ideal check is written out: if every generator is zero (including an empty list), zero divides them all and the assumed unit conclusion is impossible in the nonzero domain A.

For Step 2 I read the statements of the regular-ring definition and ring Krull-dimension definition. The first supplies the local Noetherian setting, the second defines dimension as the supremum of strict prime-chain lengths. Using the elementary local-ring description that elements outside the maximal ideal are units, a proper ideal is contained in the maximal ideal. If a nonmaximal prime above the now nonzero J had an intermediate nonzero prime, the displayed chain from zero through that prime and our prime to the maximal ideal would have length 3. All four ideals are prime: zero by Step 1, the two given primes by construction, and the maximal ideal by maximality. Thus this is an elementary chain argument, not an unstated dimension formula or a new height comparison lemma.

For Step 3 I read the whole statement of lem-trf-ufd-height-one. It is the equivalence for Noetherian integral domains, and Step 1 provides both conditions as well as its UFD side. The notion of height one in that statement is exactly the nonzero/no-intermediate-prime property proved in Step 2. A principal prime over J makes its generator divide every g_i; the hypothesis then makes the generator a unit, contradicting that the prime is proper. This proves the item rather than passing the item to another node.

For Step 4 I read the whole statement of lem-weil-pbc-zero-locus-eq-iff-radical-eq. It explicitly asserts the intersection of ALL primes containing J equals its radical, for any commutative ring. The maximal ideal itself contains J, so the intersection is nonempty and is exactly that maximal ideal after Step 3. No Noetherian assumption is needed for this citation. All citations have literal extracts in citations.json; none uses only a definition node to justify a theorem.

I checked the B–E return categories against the final JSON: there are no new statements needing sources or definition dependencies, no invented Mathlib leaf, no moved clause or unsplit proof sketch, and no new dependency that relies on this item (the existing regular-local UFD node's dependencies were read). The proof follows the existing 0C48 gcd/height-one route. The two off-chapter proof citations besides the regular definition are Mathlib leaves, so no off-unit tool declaration is needed. Each proof step is below 2000 characters and contains no hidden general comparison argument.

Small cases: in k[[x,y]], generators (x,y) and (x^2,y^2) have maximal radical, whereas a unit generator gives J=A. A single nonunit generator and the list (x,xy) violate the common-divisor hypothesis, as required. Empty and all-zero lists also violate it; dimension two guarantees that A is nonzero, and zero cannot be a unit. Rings of dimension 3 would allow (x,y) with smaller radical; the chain argument uses the actual dimension-two hypothesis and does not falsely generalize it.
