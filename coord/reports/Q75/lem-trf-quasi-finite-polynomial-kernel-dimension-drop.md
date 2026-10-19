# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-quasi-finite-polynomial-kernel-dimension-drop.json: statement split into six proof steps; statement and statement dependencies unchanged; no exact Mathlib match.
- citations.json: verbatim statement quotations for every dependency used by every proof step.
- searches.jsonl: the search command's original log; all five new queries are copied exactly into the item's mathlib_searches. Earlier Q140 searches retained.

No new nodes and no new Mathlib leaves. prepare.py is a sandbox-only preparation script, not a DAG delivery file.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 by the blueprint id and by quasi-finite, polynomial, kernel, and dimension wording. The project has quasi-finite geometry and normalization declarations, but no declaration stating this item exactly. The partial domain/dimension-drop node lem-wf-affine-dimension-drop is not an attachment for this item: its recorded Lean declaration only proves a domain criterion and its statement does not compare the dimension of a quasi-finite source with the kernel quotient. No master sorry declaration was treated as finished.

## WANTED

None. All sources needed were available in literature/stacks-project/algebra.tex.

## Findings and changes

The imported item was true but had no proof. Its source is precisely the final inference in Stacks Tag 00QK, label lemma-finite-type-domain-over-valuation-ring-dim-fibres: a nonzero kernel in the residue-field polynomial chart forces dimension less than n. I retain the full general field-algebra statement and its empty-spectrum convention. No STATEMENT-DISPUTED correction is needed. No target statement, coefficient category, or base-change morphism changes.

The split makes the quotient essential: applying 00QF directly to k[t_1,...,t_n] only gives the weak bound n. Instead 00PN preserves quasi-finiteness on factoring through R=P/ker(phi), and the prime chains of R are shorter by one because all their lifted primes contain a fixed nonzero polynomial. This is the argument behind the strictness; it is not moved into a restatement node. The quotient-prime-chain argument is elementary and written out, so it creates no node.

I searched the full DAG's statements and titles for quasi-finite dimension inequalities, strict dimension drop, nonzero ideals, polynomial quotients and kernel bounds; inspected the existing 00QF and 00QG nodes and lem-wf-affine-dimension-drop; ran blueprint_refs.py ancestor and searches for nonzero polynomial kernel dimension, dimension drop, and quasi-finite. No blueprint node states this item exactly; same_as remains empty. No new node was needed, so there are no new/existing duplicate pairs.

Mathlib searches: LeanFinder with two distinct phrasings, Loogle, grep in RingTheory, and LeanSearch, all via the required msearch.py command. The returned MvPolynomial.ringKrullDim_of_isNoetherianRing and ringKrullDim_quotient_succ_le_of_nonZeroDivisor are ingredients only. I read Polynomial.lean:120 onward, NonZeroDivisors.lean:30-50 and Basic.lean:45-65. They give the polynomial dimension, a principal quotient bound and quotient monotonicity; none states the quasi-finite target estimate. There is no exact match or one-line specialization for the item. The polynomial dimension ingredient already has the Mathlib leaf lem-sf-noetherian-polynomial-dimension, which is reused.

## Tool uses

Declared in split_report.tool_uses: lem-weil-pbc-quasi-finite-four-rings (00PN) and lem-weil-pbc-dimension-inequality-quasi-finite (00QF). They are generic commutative-algebra tools used in the 00QK inference, not replacements for the unit's contracting-correspondence or semistable-alteration route. Remaining cited statements are definitions or existing Mathlib leaves. Read the chapter sec-trace-formula and unit sk-i-curve-zero; this item is a subordinate algebra input through its existing ancestry, not the key statement of that unit. No unit realization record changes.

## Unfinished work

None at the split level. No Lean was written and no compiler, Lake, or build tool was run.

## Review by Q75

I read Stacks algebra.tex at Tag 00QK (lemma-finite-type-domain-over-valuation-ring-dim-fibres), including its complete statement and proof, and checked its tag against tags/tags. The item extracts just the field-algebra inference from its last sentence; neither integrality of T nor injectivity of the polynomial map is assumed, and the proof never uses either. I also read 00PN (lemma-four-rings), 00QF (lemma-dimension-inequality-quasi-finite), and 00QG (lemma-dimension-quasi-finite-over-polynomial-algebra), as well as the source polynomial-dimension input 00OP. There are no new-node sources to verify.

For step 1 I checked that def-weil-pbc-krull-dimension-ring really includes the empty-spectrum/zero-ring convention. The n=0 argument uses a nonzero constant's inverse and does not assume the structure map into the zero ring is injective. For step 2 I opened lem-sf-noetherian-polynomial-dimension: it gives dim P=dim k+n for a Noetherian coefficient ring, including zero variables. A field is Noetherian by its two ideals and has exactly one prime. The additional domain assertion is justified by the explicit largest-monomial multiplication argument using def-weil-pbc-mv-polynomial-ring; it is not taken from a definition that fails to state it.

For step 3 I opened the full statement of lem-weil-pbc-quasi-finite-four-rings and checked each hypothesis against the square P -> T, P -> R, R -> T, T -> T. The top map is finite type by the item's hypothesis, the square commutes by the kernel quotient formula, and every element t=t*1 satisfies the node's finite-sum hypothesis. The prime pulled back through the identity T -> T is the same prime at which quasi-finiteness was supplied. This node explicitly gives both finite type and quasi-finiteness for R -> T, so no tensor-preservation or quotient-descent theorem is used without citation.

For step 4 I checked the prime-chain definition in def-weil-pbc-krull-dimension-ring. Pulling primes back to P preserves primality by the product test and preserves strictness by surjectivity; I wrote both checks in the step. The nonzero kernel element belongs to the first lifted prime, so prepending (0) is strictly increasing. This gives length <= n-1 uniformly, not merely a pointwise strict inequality whose supremum could reach n. The argument is a few-line elementary consequence of the earlier domain and dimension calculation.

For step 5 I read lem-weil-pbc-localization-dimension-chains-below-prime: its statement gives exactly the supremum of lengths of prime chains ending below the prime. I use it to bound dim R_r by the uniform bound in step 4. I read lem-weil-pbc-dimension-inequality-quasi-finite: it applies to arbitrary commutative rings with a finite type map quasi-finite at the specified prime. Those hypotheses were established in step 3; there is no hidden Noetherian assumption on R or T. Its conclusion is exactly dim T_q <= dim R_r.

For step 6 I again checked the localization-chain statement, now for T and the last prime of each chain; it bounds that chain's length by dim T_q. The chain-supremum definition then gives the ring bound. I read lem-weil-pbc-spec-topological-krull-dimension-ring and verified its statement gives the equality for all commutative rings, including zero, needed to obtain the topological conclusion. citations.json quotes the actual statements opened for each use; no proof of a cited node is substituted for its statement.

I checked delivery-errors B through E point by point. There are no statement-only new nodes, duplicate nodes, invented search records, hollow objects, uncited non-elementary facts, cyclic uses, or clauses relabelled as new lemmas. Every non-elementary step is under 2000 characters. The proof handles T=0, n=0, a constant nonzero relation (which forces T=0), n=1 with a nonzero polynomial quotient (dimension at most zero), and the reducible example k[x,y]/(xy) (dimension at most one). The identity polynomial map has zero kernel and is correctly excluded. These checks required no correction of the statement. The main repair to the empty import was to insert the quotient and explicitly verify 00PN rather than applying the weak polynomial-source inequality and claiming strictness.
