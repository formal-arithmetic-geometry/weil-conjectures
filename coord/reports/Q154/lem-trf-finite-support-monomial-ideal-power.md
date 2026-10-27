# Q154: lem-trf-finite-support-monomial-ideal-power

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-support-monomial-ideal-power.json: statement, now split in three elementary steps. Mathlib verdict: no full match after two phrasings and reading the candidates.
- citations.json: one verbatim excerpt for the sole proof citation.
- report.md: this report. searches.jsonl is the search command's unmodified log; local PDF text and write_split.py are working aids only.

No new nodes; zero Mathlib leaves. The item statement, stmt_deps and maintainer-owned metadata are unchanged. All writing is confined to the named sandbox. No Lean, compiler, Lake, build or repository git command was run.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and for finite support, monomials and ideal powers found no declaration stating this item. Ideal.eq_zero_of_annihilated_quotient_primaryComponent (Algebra/Module/QuotientPrimaryComponentNoTorsion.lean) mentions ideal-generator products in its explanation but proves a module torsion statement. power_series_mem_combined_ideal_pow_iff (RingTheory/PowerSeriesCombinedIdealCoefficients.lean:173) concerns a specific multivariate power-series ring, not arbitrary C, P and z, and does not state the explicit finite-generator expansion. Neither is an attachment.

## Literature wanted

None.

## Issues found and changes

The item was statement-only with searches from its creation by Q78, not an earlier completed Q154 split. Its statement is true and needs no correction. Its source accurately labels this as an agent-supplied auxiliary argument rather than a theorem of ILO. I retained the statement, existing search records, source, blueprint ancestry and dependencies. The source context is ILO Exposé VI 1.6(i)--(ii), printed p. 70; it supplies completed formal monoid models, not this elementary expansion. Accordingly proof_origin.by is agent. No SGA source is used.

The induction now explicitly establishes both directions of the generator assertion, including degree zero and the empty generating list. The homomorphism calculation is an equality of finite sums and products, followed by exact counting of n ideal factors. No conclusion about infinite series, convolution, monoid positivity, cancellation, or maximum decomposition length is invoked. These are deliberately absent from the item's hypotheses and unnecessary for this finite argument.

## Unfinished work

None within this item's stage-1 scope. There are no new statement-only obligations.

## Not duplicates

No new nodes are proposed. Before deciding this, I searched the whole DAG's statements for the finite generator/product assertion, and the imported blueprint using tools/blueprint_refs.py search with “ideal power”, “monomial”, and “products of generators”. The last query has zero matches; the monomial matches concern polynomial, projective-space and Rees statements. No imported blueprint node states this item. Its blueprint.same_as remains []. The existing associated-graded-ring definition is reused for its explicit ideal-power recursion, not duplicated.

## Review by Q154

I read the chapter sec-trace-formula and unit sk-i-curve-zero, the current blueprint/latest statement and proof of lem-trf-local-term-locality, the delivered parent lem-trf-finite-pattern-factorization, and ILO VI 1.6(i)--(ii) at printed p. 70 (the paragraphs giving equal- and mixed-characteristic formal monoid models). The item's blueprint ancestor and place are already specific, and this split realizes the low-length finite part used in step 2 of its parent. It does not change the contracting-correspondence route. No new node needs a separate source review.

For step 1, I opened def-weil-pbc-associated-graded-ring and checked its actual statement: it explicitly says “$J^0=A$, $J^{k+1}=J^kJ$”. That exact excerpt is in citations.json. I use no construction or theorem concerning the associated graded ring. The finite-sum interpretation of an ideal product is the convention already given in the item. Expanding x in J^k by the induction hypothesis and y in J by its generating expression gives the claimed k+1 factor expression; the reverse containment follows because the factors are in J. The induction has its base, step, both containments and empty-list case written out. It does not borrow the conclusion from a new node or hide a non-elementary theorem.

For step 2, no node is cited or needed. The coefficient expansion was proved in step 1. A chosen decomposition is a hypothesis, not an existence assertion requiring positivity of P. Repeated application of the assumed z-addition formula gives the product, and the empty case uses the assumed z^0=1. Applying the ring homomorphism to the finite coefficient sum gives exactly the displayed expanded terms. Distributivity is the full argument. Arbitrary relations in P cause no problem: different decompositions are permitted and no uniqueness or distinct monomials is claimed.

For step 3, no node is cited or needed. Every C(t_j) is in the generating set because t_j is in J, and every monoid factor is in that set by the required nonzero hypothesis. The number of such factors is (n-l_p)+l_p=n because 0<=l_p<n. The inline finite-product convention gives membership in b^n directly. Ideal closure gives scalar multiplication and the two finite sums. This does not use flatness, an ideal-image theorem, a map-of-powers theorem or infinite convergence. All these arguments are elementary; marking them elementary records the written finite computation, not an appeal to an unstated standard lemma.

I tested k=0, k=1, h=0 with k>0, n=1 (necessarily l_p=0 and p=0), S empty, P={0}, J=0, J=A and the zero ring. For h=0 all relevant k=n-l_p are positive and every coefficient is zero. A nontrivial relation example is P=Z/2: 0 can be a sum of two nonzero elements; the same factor count works (the combined ideal then contains a unit and can be the whole ring). Thus neither positivity nor cancellation is being smuggled into the proof. A monoid with a length-two and length-three expression for the same p also satisfies the argument for either chosen length.

I checked delivery-errors B through E against the files: no new nodes duplicate a clause or elementary assertion; statements retain their own objects and inline conventions; no nonexistent definition or theorem is cited; citations use statements rather than proofs; no self-reference or dependency cycle is introduced; no missing hypotheses or object substitutions occur. The one citation was verified verbatim against the current repository. The proof steps are respectively 806, 570 and 604 characters, below the long-step threshold, and their full sum is 1980 characters. No helper lemma is hidden in them. The item's one off-unit dependency is a definition used only for notation already present in stmt_deps; it is not a replacement proof route.

For Mathlib, I read all seven Q78 search summaries retained in the item, and ran the seven additional searches in searches.jsonl. The full command outputs were read. LeanSearch and LeanFinder returned ideal finite-generation, Rees, ideal-power and polynomial coefficient results. Loogle returned Ideal.prod_span and Ideal.mem_span_pow_iff_exists_isHomogeneous among its candidates. I read Ideal.prod_span in Mathlib/RingTheory/Ideal/Operations.lean:629 and Ideal.mem_span_pow_iff_exists_isHomogeneous in Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:671. They supply related generator/span results, but neither states the finite sum with an arbitrary monoid map and chosen varying lengths, and deriving the explicit asserted expansion requires the induction and substitution written here. I did not create an elementary generator lemma merely to make it a Mathlib leaf. The original rate-limited LeanSearch record remains unavailable as originally logged; the new LeanSearch succeeded. No searches were fabricated or repeated merely to replace an unavailable service.

The first dry run required a citation excerpt of at least 40 characters. I expanded the same verbatim excerpt to include the surrounding A and J hypotheses, verified it again in the cited statement, and reran the dry run. No mathematical correction was needed.
