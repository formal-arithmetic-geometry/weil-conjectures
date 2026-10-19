# Q84 — lem-trf-fibre-associated-primes-module-ring

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-associated-primes-module-ring.json`: existing statement, split into four steps; no Mathlib match.
- `citations.json`: five verbatim statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the actual search-command log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and for associated-prime/annihilator notions. The only associatedPrimes concept hits were unrelated uses in Regular/ProjectiveDimension. No project declaration states the item, and the item has no existing Lean audit declaration to attach. Upstream master is not treated as finished evidence.

## WANTED

None. All sources needed for this argument are in the repository.

## Findings and changes

The mathematical statement is correct as written, including its stronger annihilator assertion for every element and the absence of Noetherian and flatness hypotheses. Its statement, statement dependencies, original source, ancestry and original searches are retained. The previous empty proof is replaced by the fraction calculation behind Stacks Tags 05BY and 05BZ, used in Remark 05E0. The only added dependency is the existing definition of localization at a prime, which explicitly defines the ring residue field. This avoids asking the scheme-residue-field definition to supply a fraction calculation it does not state.

I read the chapter and unit records and the current blueprint update of `lem-trf-local-term-locality`. The immediate parent `lem-trf-associated-primes-fibre-bound` uses this item at Step 4 for its S-module/fibre-ring equivalence. This delivery supplies that commutative-algebra subargument; it changes no step of the contracting-correspondence unit route. The fibre prime correspondence is an existing Mathlib leaf, so no off-unit tool exception is needed. The item is not the unit's key node and its realized fields are untouched.

The whole-blueprint searches for associated primes/associated, 05BZ and fibre ring found no blueprint node stating this module-ring comparison. DAG searches by 05BY/05BZ/05E0, fibre annihilators and the relevant notions found the item, its parent and other fibre arguments, rather than an existing general comparison to cite. No new nodes were needed. In particular, common denominators and the elementary prime-ideal calculation were kept as explicit proof steps, rather than repackaged as lemmas.

The actual Q84 Mathlib searches are recorded in searches.jsonl and appended to the inherited mathlib_searches unchanged in tool/query text. I read Basic.lean and Localization.lean in the pinned Mathlib. Despite natural-language search descriptions, Basic.lean defines association using the radical of an element annihilator; its exact-annihilator equivalence assumes a Noetherian ring. The localization equality at Localization.lean:136 also requires a Noetherian base. Neither is the arbitrary-ring statement here. A second semantic query found the useful fraction numerator theorem `Ideal.ResidueField.exists_smul_eq_tmul_one`, but it alone does not state this item; the same elementary common-denominator calculation is written in Step 1.

## Unfinished work

None for this one-level split. No new unsplit statements, Lean files, compiler calls, or changes to shared project/launcher files.

## Not duplicates

No new nodes were created.

## Review by Q84

I read algebra.tex at `lemma-ass-quotient-ring` (Tag 05BY), `lemma-localize-ass` (Tag 05BZ), and `remark-bourbaki` (Tag 05E0). Tag 05BY omits its proof; Tag 05BZ explicitly says that for an element in the localized module its two annihilators satisfy contraction and extension, and uses the localization prime correspondence. Remark 05E0 applies these two comparisons to a fibre module. I expanded those arguments directly for an arbitrary C-module rather than assume an unjustified Noetherian localization converse. There are no new-node sources to review.

Step 1 uses the actual statement of `def-weil-pbc-localization-at-prime` for fractions in A_p and its quotient residue field, and `def-weil-pbc-module-tensor-product` for tensor generation and bilinearity. These statements really supply what the step takes. The proof explicitly gives both the unit and inverse, and a common denominator and numerator for every finite sum; since p is prime the product denominator stays outside p. It does not invoke an unproved compatibility of an abstract fibre isomorphism. This is an elementary finite-sum computation, not a hidden comparison lemma.

Step 2 uses the element-annihilator formula of `def-weil-pbc-annihilator-associated-primes`, which imposes no Noetherian condition. I checked the scalar restriction identity pointwise. To show J = IC, the step proves each inclusion and multiplies by the specific unit from Step 1; no flatness or tensor exactness is used. The same-element assertion holds even for z = 0.

Step 3 cites no additional theorem: it proves properness and the product test in both directions. In the difficult direction it multiplies cd by both denominators, applies primality in B, and returns using their inverses. Thus it never assumes extension preserves arbitrary prime ideals. If I is proper then z is nonzero, so J is proper; if J is prime, contraction is proper because j preserves 1. These are exactly the hypotheses used.

Step 4 uses the exact-annihilator definition again and the statement of `lem-weil-pbc-fibre-ring-primes-bijection`, which I opened and read. That node explicitly gives injectivity of contraction on all primes of C and says their contractions in B lie over p in A. The preceding steps give existence of associated annihilators in both directions, so the prime correspondence is used only for the injectivity and fibre assertion it states. The citations file copies the actual statements verbatim. All cross-unit proof statements used here are already Mathlib leaves.

I checked delivery-errors B–E against the finished file: no new-node self-containment/search/duplicate issue, no clause relabelled as a new node, no unsupported non-elementary assertion, no use of a cited node's proof instead of its statement, and no new cycle (all proof citations are definitions or the existing fibre-correspondence leaf). I tested L = 0 and z = 0 (both annihilators are unit ideals, neither prime); A a field (C = B and the comparison is the identity); a zero fibre ring (only the zero unital module occurs); and noninjective A to B (the calculation never cancels in A or B, only multiplies by units in C). These checks explain why no flatness, finite generation or Noetherian hypothesis is needed. The four steps have fewer than 800 characters each; none contains a long hidden lemma. No statement dispute or source error was found.
