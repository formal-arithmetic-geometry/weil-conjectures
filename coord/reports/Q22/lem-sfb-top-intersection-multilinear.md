# Stage 1 report: lem-sfb-top-intersection-multilinear

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-top-intersection-multilinear.json: statement, now split in five steps; no Mathlib match for the geometric intersection pairing.
- citations.json: eight entries, one per cited node per step, checked as literal substrings of the cited statements.
- report.md: this report and signed review.

No new nodes; no new Mathlib leaves. The local write_split.py is a sandbox helper, not a delivery node.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and intersectionNumber, intersection_number, intersection multilinearity and additivity. No project declaration states this item. The existing lean/Sheaf/AlgebraicGeometry/IntersectionNumber.lean supplies the coefficient definition only, not these assertions.

## WANTED

None. Read literature/stacks-project/varieties.tex, labels definition-intersection-number (Tag 0BEP), lemma-intersection-number-additive (Tag 0BER), and lemma-numerical-polynomial-from-euler (Tag 0BEL), including their proofs. Verified the tag mapping in literature/stacks-project/tags/tags.

## Findings and corrections

The imported item was unsplit, with no proof and no proof dependencies. Its statement is correct as written and is preserved. The very brief proof of 0BER omits the coefficient extraction: the new step 3 identifies the three substitutions of one polynomial and enumerates exactly the two monomials that can contribute. Symmetry and isomorphism invariance follow from the defining polynomial. The zero, dual and rational extension clauses now have explicit arguments; the rational extension is the vector-space quotient by the stated tensor relations, not an implicit choice of representatives.

I read the chapter and unit records, SETUP's three levels, GOAL.md, the worker/stage-1 rules, and both occurrences of delivery-errors B--E. The current latest blueprint's sk-thm-sf-ctf-stability direct-image proof uses compactification in (3); the item's historical blueprint provenance records an older alteration reduction. This split concerns only the generic intersection-theory input already requested by the reviewed lem-sfb-abelian-degree-polynomial; it neither changes that provenance nor replaces the current unit proof. There is no released repair note for this item.

The existing lem-sc-snapper-numerical-polynomial supplies arbitrary-length lists of invertible modules and the total-degree bound; I declare that generic off-unit tool use. The existing lem-trf-polynomial-infinite-evaluation-identity is a Mathlib leaf, so needs no off-unit route exception. Its statement is for any integral domain, hence applies over Q; its origin in a trace-formula branch is irrelevant to this algebraic specialization. No trace, duality or purity assertion is used.

## Mathlib and duplicate searches

The msearch.py log records the actual Loogle, LeanFinder, LeanSearch and grep queries for this item, including a second semantic phrasing and second name/grep patterns. The searches returned covers, ordinary tensor algebra, ring Picard groups, incidence-algebra Euler characteristics, and root-system coefficients; none concerns the top intersection coefficient of a proper scheme. Earlier inherited searches remain intact. Read the late LeanFinder result from searches.jsonl after its tool session disappeared: CommRing.Pic.mk_tensor and mul_eq_tensor concern Picard groups of rings, and do not supply this scheme intersection pairing. The new search results are recorded with the original query texts and actual hit names.

Searched dag/nodes for 0BER and 0BEP, intersection numbers, and polynomial identity/lattice uniqueness statements; searched the whole blueprint index using blueprint_refs.py for intersection, numerical polynomial and multilinear. The relevant existing inputs are def-sc-intersection-number and lem-sc-snapper-numerical-polynomial. Reused them rather than creating duplicates. No new node is a renamed clause of the item or a simple specialization.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs to distinguish.

## Review by Q22

I checked the argument against Stacks 0BER with its dependencies 0BEL and 0BEP open. These are the item's sources; there are no new nodes requiring additional sources. The general polynomial identity node was opened in full, and I read the actual Polynomial.eq_of_infinite_eval_eq declaration in Mathlib/Algebra/Polynomial/Roots.lean:156. I read the statements of every cited node in full before constructing citations.json.

Step 1 uses def-sc-intersection-number for exactly the coefficient convention, identity-closed-immersion specialization, coherence and support dimension appearing in its statement. It uses lem-sc-snapper-numerical-polynomial for existence and the degree bound for an arbitrary finite list, including g+1 entries. Properness, field coefficients, invertibility, and the coherent module O_X all agree with its hypotheses. I supplied the induction reducing polynomial identity on the integer grid to lem-trf-polynomial-infinite-evaluation-identity over Q. The base is constants, and the inductive coefficients vanish on the entire smaller grid. There is no assertion of polynomial identity over the possibly finite ground field k: the polynomials have rational coefficients.

Step 2 uses def-pc-euler-characteristic for the alternating sum of cohomology dimensions, and def-sc-intersection-number for extraction of the product coefficient. A cohomology functor sends an isomorphism to an isomorphism, so this preserves each dimension. Reordering factors uses the actual tensor symmetry of modules; reordering variables fixes the product monomial. These are elementary functoriality and coefficient facts, not a new intersection-theory theorem assumed without citation.

Step 3 uses lem-sc-snapper-numerical-polynomial for the g+1-variable polynomial Q and def-sc-intersection-number to identify the three coefficients. Tensor powers of a tensor product agree for all integer powers; negative powers use the inverse line bundle, and this is checked on rank-one local frames. The equality of polynomials follows from step 1, not from a hidden base-change or comparison result. In the monomial expansion, the other g-1 exponents must each be 1, and the two replaced exponents must sum to 1, giving exactly (1,0) or (0,1), with coefficient 1. This carries the additivity argument rather than moving it to a new node.

Step 4 uses def-sc-invertible-module for rank-one local trivializations and the definition of the dual. The evaluation morphism is an isomorphism on every such trivialization, explicitly multiplication of two free rank-one modules, hence globally an isomorphism. The zero and negative formulas then follow by subtraction from additivity in Q. No assumption that an arbitrary locally free module has rank one was added.

Step 5 cites no new fact: it constructs the extension as an explicit finite sum. The tensor relation in a chosen slot maps to zero by step 3; multiplying such a relation by a rational scalar and summing still maps to zero. Thus the expression descends to the stated quotient, and expansion proves uniqueness and symmetry. It requires neither freeness nor torsion-freeness of the Picard group, and remains valid if every line bundle is torsion.

I tested g=1 (there are no t variables in step 3), a trivial entry, dual entries, torsion classes (additivity gives mI=0 and hence I=0 in Q), dimension g with smaller-dimensional components (Snapper only requires the support dimension bound, not purity), and finite ground fields (polynomial uniqueness occurs over Q). For g=0 the zero-slot language would have no meaning, and the item's explicit g>=1 excludes that case. No statement dispute or missing hypothesis was found.

All proof steps have explicit elementary flags and source places. The union of uses is exactly proof_deps. All eight quotes are verbatim and every use says what is taken from it. There are no new nodes, no hollow definitions, no SGA source, and no new dependency back to the item. No step is longer than 2000 characters, and no concealed standalone geometric comparison is left in one. I corrected no statement: the repair was completing the coefficient calculation and extension proof. The required server-only dry run passed at 6353c3b566c. After recording the final Picard-group grep and reading its declarations at Mathlib/RingTheory/PicardGroup.lean:504 and :519, I rerun the dry run before direct delivery.

## Unfinished work

None within this one-level stage-1 split. The reused Snapper node's downstream formalization is not asserted to be complete; no sorry-containing source declaration is offered as an attachment.
