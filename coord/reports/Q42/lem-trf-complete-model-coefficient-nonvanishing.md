# Q42 stage-1 delivery: lem-trf-complete-model-coefficient-nonvanishing

## Files written

- dag/nodes/sec-trace-formula/lem-trf-complete-model-coefficient-nonvanishing.json: statement item, split; no exact Mathlib match. Statement unchanged.
- citations.json: seven literal statement excerpts covering every cited node in every proof step.
- report.md: this report.

No new nodes and no new Mathlib leaves. Existing lem-trf-monoid-completion-coefficients already states the full coefficient-family identification, including finite convolution and the images of individual monomials. Creating it again would be a duplicate.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, completed monoid algebra, coefficient nonvanishing, and monoid/completion terminology. No declaration states every clause. The Mathlib candidate MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff concerns free multivariate power series and non-zero-divisibility of a series, not this completed arbitrary positive monoid algebra and survival of monomials in its quotient.

## WANTED

None. All literature used is present.

## Findings and corrections

The imported item is a statement-only auxiliary node created in the Q138 re-split of lem-trf-complete-toric-facet-valuations. No proof or report existed in this item sandbox. I copied the current item, preserved its statement, source, blueprint ancestry, creation fields, and all earlier Mathlib search records. The statement is true with its stated hypotheses; no STATEMENT-DISPUTED correction is needed.

The source explicitly labels this as an agent refinement, not a theorem asserted by ILO. I read ILO Exposé VI 1.6(i)--(ii), printed p. 70, PDF page 76, using pdftotext on PDF pages 75--76. It displays the equal-characteristic completed monoid model and the mixed-characteristic quotient by f congruent to p modulo the monomial/parameter ideal. It does not prove the arbitrary complete-local-domain coefficient assertion; proof_origin is therefore agent. I also read Stacks algebra.tex, Tag 00FN, label lemma-Noetherian-permanence, including its quotient proof; and Tag 0316, label lemma-completion-Noetherian-Noetherian. No SGA source was used.

The current latest blueprint (COMMITS.txt: main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345) has no separate theorem for this algebra. I read its lem-trf-local-term-locality statement and proof and the recorded sk-i-curve-zero unit/chapter. I retain the inherited proof-(1)--(2) ancestry through complete-local log-regular recognition; this split changes no unit or chapter route. Blueprint searches for monoid, monoid completion, coefficient families, monomial survival and nonunit constant found no imported exact theorem. DAG searches by coefficient-family, finite-convolution, monoid-algebra and completion keywords found the existing coefficient theorem, which is used instead of making new nodes. Searches by 00FN and 0316 found the existing Noetherianity nodes.

## Review by Q42

I checked the node files and sources against delivery-errors B--E, including the repeated checklist. There is no new statement-only node to audit for hidden proofs, duplicate tags or missing definitions. The item introduces all its objects, and its existing statement dependencies define completion, adic completeness and Noetherianity. The local domain, lattice, finitely generated submonoid, positive weight and multiplication are introduced explicitly. The split has no hidden comparison of coefficient categories or derived objects.

Step 1 uses lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-adic-completion-noetherian. I read both complete statements: the former applies to any commutative finite-type algebra over a Noetherian ring; the latter applies to completion at any ideal of a Noetherian ring. The finite-type presentation is not merely asserted: the step defines the map from the polynomial ring on a finite generating list and proves surjectivity on each monomial and finite sum. A nonzero generating list is obtained by deleting zero entries. Its empty-list case gives A when T={0}. The base A is Noetherian by hypothesis and J is exactly the ideal in the item. The completion theorem is a generic off-unit tool, declared in split_report.tool_uses; the finite-type theorem is already a Mathlib leaf. Stacks 00FN and 0316 are the sources actually read for this step.

Step 2 uses lem-trf-monoid-completion-coefficients. I read its statement in full, not just the proof or title. It assumes a complete separated Noetherian local ring and a finitely generated monoid embedded in a finite-rank free abelian group with positive weight, precisely the hypotheses here (the domain assumption is stronger). Its conclusion explicitly supplies the A-algebra isomorphism, finite convolution, and the coefficient of az^u. We need none of its additional assertions about kernels or finite quotient modules. Thus this citation really supplies the formulas later used. Its source is expressly the agent coefficient refinement of ILO VI 1.6, not a claim that ILO itself states it.

Step 3 uses that same statement's finite convolution. I checked the induction with a fixed threshold N=W(u): all weights in T are nonnegative integers; for a+c=v with a nonzero, W(c)=W(v)-W(a)<W(v). The induction claim covers every exponent at a given weight, so ties in weight cause no problem. In weight zero, positivity excludes all a other than zero; in each successor stage all other summands vanish and cancellation of the nonzero r is justified by the domain assumption. This is a direct induction on a finite convolution formula, not an appeal to an unstated formal-series lemma; it stays as an elementary proof step. There is no use of a total ordering of T or an unproved embedding into a free positive monoid.

Step 4 again uses only the cited convolution formula, the weight identity and the vanishing already proved. This explicitly gives the coefficient at the threshold, even if other exponents have the same weight: their possible contributions require a positive-weight first exponent and hence a strictly lower-weight second exponent. No coefficient change or convergence assertion is being hidden.

Step 5 uses lem-weil-pbc-surjective-image-noetherian, whose statement I read: any surjective commutative-ring homomorphism with Noetherian source has Noetherian target. The quotient map satisfies those hypotheses by Step 1. The monomial formula is explicitly supplied by lem-trf-monoid-completion-coefficients, so theta*b=z^u gives exactly the required zero coefficients below W(u) and coefficient one at u. Membership in a principal ideal combines a finite sum of multiples into one multiple. Steps 3--4 give 1=r*b_u. Since r is in the proper maximal ideal, multiplication by b_u stays in that ideal, contradicting properness. This is written out and does not invoke a new theorem restating the monomial-survival clause.

Step 6 uses the earlier steps and no node beyond them. I tested T={0}, u=0, the zero-weight threshold, A a field (the r-hypothesis is then empty), theta=r, and theta=r+z^g. In the latter case the coefficient recursion would require division by the nonunit r if a monomial were in the principal ideal; the proof's contradiction agrees. I checked T=N^2 with equal-weight exponents and the nonfree monoid generated by 2 and 3 inside Z: the proof uses positivity and finite convolution, not unique generator decompositions or additivity of the maximum decomposition length. I also checked why both r!=0 and r in m matter: the first permits cancellation and the second excludes 1=r*b_u. A zero divisor or a unit would invalidate those inferences, and neither is allowed.

Every uses entry has a verbatim quote in citations.json, checked by substring comparison against the current node statement. All non-elementary inputs are existing cited nodes, no cycle to the item occurs in their statements or immediate proof dependencies, and the server global check is required below. proof_deps is exactly the union of uses. Every step is below 2000 characters (largest 588), so there is no long step hiding an extracted lemma. There is no new node which repeats an item clause and no inline proof in a new statement. TeX strings use single backslashes after JSON decoding, and the inherited statement is unchanged.

Mathlib searches were run only with the required msearch.py wrapper and read as returned. The five Q42 searches are recorded in searches.jsonl and appended to the item's existing search evidence: two LeanFinder phrasings, Loogle, grep, and LeanSearch. All services answered successfully. The first semantic search returned one-variable Weierstrass division/preparation, whose residue-series hypothesis and objects differ; the second returned free-monoid weighted-order formulas. I read Mathlib/RingTheory/MvPowerSeries/NoZeroDivisors.lean:54--101 for the nearest constant-coefficient non-zero-divisor candidate. It gives no one-line specialization to this item's arbitrary monoid completion and quotient monomial-survival conclusion.

## Unfinished work

None within this one-level split. Existing dependencies remain their own items. No Lean was written or compiled, and no repository or launcher file was changed.

## Validation

The required server dry run and direct delivery are performed after this report is written; their output is the authoritative validation record.
