# Q35: lem-trf-monogenic-quotient-height-drop

1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-monogenic-quotient-height-drop.json`: statement, split into five proof steps; no whole-item Mathlib match.
- `citations.json`: verbatim statement quotations for every use in the five steps.
- `report.md`: this report. Searches were logged by the required command in `searches.jsonl`.
- No new nodes; no new Mathlib leaves. The proof reuses three existing Mathlib theorem leaves and three existing definition leaves.

2. Attachments

None. Searches in `lean/WeilConjectures/` for the exact id and blueprint tag found no declaration. Concept searches for monogenic kernels, quotient heights and finite fraction fields found related Nagata and polynomial-quotient dimension statements, not the whole assertion under these hypotheses. In particular `AlgebraicGeometry.topologicalKrullDimAt_polynomial_quotient_eq_height_difference` is about finitely many variables over a field, not a general Noetherian domain, and does not give generic algebraicity or this strict drop. No Lean was written or compiled.

3. Wanted literature

WANTED: none. All sources used are present.

4. Problems in the item, blueprint, or brief

No statement dispute. The statement and `stmt_deps` are unchanged. The imported node was a sound, statement-only extraction of Case II of Stacks 02IJ. Its proof needed the missing elementary generic-field, residue-field, and prime-chain arguments. The source's assertion trdeg_R(S)=0 needs denominator clearing; algebraic over Frac(R) alone is not literally the ring-algebra definition cited in this node. Step 3 supplies that argument without changing the meaning of the statement.

The blueprint ancestry and unit sk-i-curve-zero are kept. This generic commutative algebra sublemma belongs to the existing dimension-formula input; it does not alter the contracting-correspondence route of the unit or cite any SGA source. It is not a key node of the unit, so no unit record is edited.

5. Unfinished work

None in this stage-1 item. The existing theorem leaves are reused, not resplit; no statement-only child is needed.

## Search record and leaf decision

Read the inherited six searches and their results, and retained them. Ran the required msearch.py command for this item with leanfinder (two phrasings), loogle, grep and leansearch. The queries and actual result summaries are appended to `mathlib_searches`, exactly as recorded in `searches.jsonl`.

The whole item is not a one-line specialization of a hit. `Polynomial.height_eq_height_add_one` assumes a maximal polynomial prime; the item's Q is any prime. The Krull-height quotient bound returned by grep has the other direction and a number-of-generators term. `instFiniteDimensionalFractionRingOfFinite` assumes that S is module-finite over R, which the item does not assume (Z[1/2] is an example). Quasi-finite residue-field results need quasi-finiteness. `Algebra.trdeg_eq_zero` applies only after algebraicity has been proved. The existing algebraic-generators-finite-extension leaf supplies precisely the needed generic-field theorem.

I read Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean around `finiteDimensional_adjoin`, Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean around `Algebra.IsIntegral.of_finite`, and Mathlib/Algebra/MvPolynomial/Basic.lean around its IsDomain instance, confirming the reused theorem leaves. This was source reading only.

## Not duplicates

No new node is proposed. Searched the whole DAG by algebraic-generator, simple-extension, quotient-residue, height-drop and finite-field-extension notions, and by Tags 02IJ, 09GH and 09GG. Blueprint searches for monogenic, monogenic quotient, quotient height, height drop and algebraic generators returned no equivalent blueprint statement. Existing lem-weil-pbc-algebraic-generators-finite-extension, lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-polynomial-ring-domain are cited directly. The elementary quotient isomorphism is proved explicitly, rather than creating a second version of lem-weil-pbc-quotient-residue-field. Its statement was also read: it only concerns an iterated ring quotient, so it was not cited for the field/base compatibility.

## Review by Q35

I read Stacks algebra.tex, Tag 02IJ (algebra-lemma-dimension-formula), in full through Case II. The source reduces a one-generator domain algebra to a polynomial quotient, asserts generic trdeg zero and uses the strict drop of dimension. I also read fields.tex, Tag 09GH (fields-lemma-algebraic-finitely-generated), and algebra.tex, Tag 00GK (algebra-lemma-finite-is-integral), and the prime-chain paragraph of algebra-lemma-one-equation. The proof keeps that route and spells out its omitted verifications. There are no new nodes whose source needs a separate review.

For Step 1 I opened def-weil-polynomial-ring and def-weil-algebraic-element. The former defines coefficientwise polynomials, the latter defines algebraicity by a nonzero annihilating polynomial. Injectivity R -> S and the domain hypotheses give K -> L; injectivity R -> K preserves a nonzero coefficient of P, so the relation is a nonzero polynomial over K. No integrality over R is asserted.

For Step 2 I opened lem-weil-pbc-algebraic-generators-finite-extension. Its statement gives finite dimension of the field generated by finitely many algebraic elements, precisely with K a field and x an algebraic element of L as Step 1 established. I proved L=K(x) using surjectivity and fractions, instead of taking this identification from the proof of the cited leaf. Thus the cited statement supplies exactly the remaining finiteness assertion.

For Step 3 I opened lem-weil-pbc-finite-algebra-is-integral and def-kun-transcendence-degree. L is now a finite-dimensional K-vector space and therefore a finitely generated K-module, as the first statement requires. Its conclusion provides a monic annihilating polynomial for every y in S (viewed in L). The finite product of its nonzero coefficient denominators is nonzero in R; multiplying gives a nonzero polynomial in R[U], with leading coefficient that product. The injection S -> L returns its vanishing to S. Every nonempty subset then has a one-variable relation, so the supremum in the definition of trdeg is zero. This avoids treating a definition as a theorem about fraction fields.

Step 4 cites no node. I checked both directions of the quotient bijection directly from Q=f^{-1}(q) and surjectivity; then wrote the fraction formula, its inverse and its restriction to fractions of R/p. The fields are Frac(A/Q) and Frac(S/q), not quotient rings or localizations mistakenly identified without proof. This elementary construction proves the required compatibility over kappa(p), not merely an abstract field isomorphism.

For Step 5 I opened lem-weil-pbc-polynomial-ring-domain: its general statement includes the one-variable polynomial ring. It gives that zero is prime in A. Pullback primeness follows by applying f to a product; strictness follows by lifting an element of the difference of the target primes. Each pulled-back prime contains the same nonzero kernel, so zero can be prepended strictly. The finite-supremum case uses an attained integer maximum and the unbounded case produces unbounded lifted chains; no unproved finite-height theorem or cancellation of infinity is being used. The elementary flag covers this explicit chain argument, not an application of an unrecorded dimension theorem.

I checked delivery-errors B--E point by point. All objects and notions in the unchanged statement are introduced there or by its existing definition dependencies. No new unsplit node contains a proof or duplicates a clause; there are no new nodes. Every non-elementary inference is exactly the statement of a cited theorem leaf. All quoted citations were taken verbatim from those statements. The only other steps are explicit constructions from definitions; there is no hidden normality, catenarity, separability, quasi-finiteness or module-finiteness assumption on S/R. All five steps are shorter than 2000 characters. There is no dependency on the parent dimension inequality, hence no cycle through the item.

Small cases: R=k, S=k and f(T)=a give degree one, trdeg zero, q=0, Q=(T-a), and the strict drop 0+1=1. An irreducible polynomial of degree d>1 over k gives finite degree d with the same height behavior. For R=Z and S=Z, f(T)=0, q=(p) gives Q=(p,T), so the chain proof gives height at least two. For Z[T] -> Z[1/2], T -> 1/2, kernel (2T-1), the fraction extension is Q/Q but the map is not module-finite, verifying why integrality over R must not be inferred. At q=(3), Q=(3,2T-1), the residue fields are F_3 and the height drop is one; at q=0, Q is the nonzero kernel and the zero-prime prefix still works. Inseparable irreducible polynomials are allowed because the proof uses algebraicity only. A zero polynomial kernel is excluded: k[T] itself would have trdeg one and no strict height drop. Nonzero domain assumptions exclude the zero-ring failure of coefficient and fraction-field embeddings.

The correction I made during self-review was to use the existing finite-algebra-is-integral theorem for algebraicity of arbitrary elements of L, rather than leaving that substantive implication behind an elementary flag. I also wrote out the quotient map over R/p and the infinite-supremum alternative for prime heights, so neither compatibility nor a height-finiteness assertion is hidden.


## Repair of the landing return (2026-10-23)

The returned head is `506f1dc79a2`, recorded in `coord/returns/Q35.md` on 2026-10-22 at 14:44 UTC. Its mathematical review passed; the landing failed because the side completion had not been promoted to the live DAG. I retained that delivery's five-step proof, report, citations, and logged searches, and compared the retained node with the current read-clone node. The current item is `unsplit`, has no proof or review, and has exactly the same statement, statement dependencies, creation metadata, chapter, unit, and blueprint ancestry. The split therefore remains work to deliver, rather than an already-landed item to overwrite. The delivery tool performs the rebase in its own worktree; I ran no git command in the shared repository.

I first ran the required dry run on the retained packet; it exited successfully with `OK (not pushed)` at `1b4ebae6503`. I then reopened every current cited node, including all three statement definitions and all six proof dependencies. Each of the six proof quotations in `citations.json` still equals the cited node's entire current statement. Every cited proof node remains an unmerged Mathlib leaf. Thus there is no changed theorem statement requiring a dependency substitution: polynomial coefficients and algebraicity still justify Step 1, finite algebraic generators Step 2, finite-algebra integrality and the supremum definition Step 3, and the polynomial-domain assertion Step 5. The current Noetherian-ring statement still defines exactly the hypothesis of the item. I reread the source passages 02IJ/lemma-dimension-formula, 09GH/lemma-algebraic-finitely-generated, 00GK/lemma-finite-is-integral, and the prime-chain paragraph of lemma-one-equation. I also reread the three recorded Mathlib theorem declarations and checked the related project polynomial-quotient declaration: its field-base hypotheses and different conclusion still prevent attaching it to this item.

This packet is not an unchanged re-push. In Step 4 I made explicit that the kernels of both coefficient maps to the quotient rings are exactly p; hence both embeddings of R/p exist and the induced fraction-field isomorphism respects their common fraction field kappa(p). In Step 5 I made explicit the length-zero chain ensuring that a bounded set of chain lengths is nonempty before taking its attained integer maximum. These are clarifications of the retained arguments, with no change of statement or proof route. The split report now records this repair and its current dependency audit. No new node was created, and the search questions have not changed, so the recorded searches were read and reused rather than repeated.

Under my Review by Q35 above, I rechecked B--E on this repaired packet: the residue fields are fractions of A/Q and S/q, the coefficient field is Frac(R/p), and each quotient coefficient map is injective for the stated reason. Strict chain lifting uses surjectivity and the common nonzero kernel, not any unproved catenarity or finite-height assertion. The bounded-chain clarification also covers q=0, while the existing unbounded argument covers infinite heights. All five steps remain below 2000 characters. The unchanged full-statement quotations still verify every node use. The only repair request was the live-DAG rebase and renewed dependency review; both are addressed here, with the final required dry run and push to follow.
