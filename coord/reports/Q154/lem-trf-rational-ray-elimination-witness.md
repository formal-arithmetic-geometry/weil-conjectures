# Stage-1 worker report: lem-trf-rational-ray-elimination-witness

## Files written

- dag/nodes/sec-trace-formula/lem-trf-rational-ray-elimination-witness.json: statement item, now split into four elementary proof steps; no full Mathlib match.
- citations.json: empty list, since no proof step uses a node citation.
- report.md: this report. The tool-generated searches.jsonl is retained.

New nodes: 0. New Mathlib leaves: 0. The finite-maximum API is not a leaf for this entire statement: signed ratio compatibility and the residual inequalities still require the explicit argument written in the item. No new node is warranted for that elementary API, nor for the two-line signed arithmetic.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, the item id, rational ray/inequality terminology, signed inequalities and Fourier-Motzkin. No project declaration supplies this item. No Lean was written or compiled.

## Wanted sources

None for this elementary auxiliary assertion. Its existing source explicitly labels it agent-written; no external theorem is claimed for it.

## Findings and corrections

The statement is correct and unchanged. The live node had no proof. I supplied the finite-list maximum construction, the exact positive-denominator comparison, membership-based upper bounds and every sign case. Existing historical searches and blueprint/source fields are preserved; six fresh searches through msearch.py are appended verbatim by tool/query, including two semantic phrasings. All returned types were read. The relevant Mathlib sources were read at Data/Finset/Max.lean:180--230 and Tactic/Linarith/Oracle/FourierMotzkin.lean:180--232. The former has only maximum properties; the latter has tactic metaprograms, not the required mathematical assertion.

The current blueprint ancestor lem-trf-local-term-locality and the sk-i-curve-zero unit were read in main-20261015, together with their DAG records and the chapter record. They contain the contracting-local-term route, not this rational arithmetic. I retained the accurate historical-ancestry explanation instead of inventing a cone clause in the blueprint. The immediate parent lem-trf-rational-cone-dual-finite actually uses this witness in proof step 4, and its hypotheses match this statement. The item is auxiliary rather than the unit key node, so no unit realization was changed. Whole-DAG statement searches and blueprint_refs.py searches for rational inequalities, finite maximum and largest found no alternate blueprint statement of this witness. No new node or route departure is introduced.

## Unfinished work

None. The required server dry run passed; this is a direct-delivery worker under the current brief, so no second worker is required before push.

## Review by Q154

I read the item and the complete statement and assembly proof of its immediate parent lem-trf-rational-cone-dual-finite. I read the cited contextual source itself: ILO, Expose VIII Remark 3.1.29, printed p. 103, says desingularization can be described combinatorially and discusses toric varieties. It does not prove this witness theorem. The item already says this explicitly; proof_origin remains by agent and each step identifies the elementary auxiliary argument rather than attributing it to that remark. No SGA source is used.

Step 1 has no cited statement. Its only inputs are finiteness of I, rational division by the strictly negative a_j, and comparison of two rationals. I wrote the recurrence starting at zero and its induction invariant: the current value belongs to the prefix and dominates the prefix. This proves finiteness, nonemptiness, attainment, maximality and both lower bounds without assuming I or I_- nonempty and without hiding a finite-maximum lemma.

Step 2 has no cited statement. I checked a_i>0 and a_j<0 before division. The denominator a_i(-a_j) is positive, and the numerator is exactly the stated pairwise expression. Thus no inequality reversal is missed. Nonnegativity of b_i, used to compare zero with the upper bound, is a separate hypothesis of this item, not an inferred condition on the negative class.

Step 3 has no cited statement. It takes the ratio bounds from Step 2 and actual membership T in B from Step 1; an arbitrary upper bound of B would not suffice for this inference. Every element of B is zero or a negative-sign ratio, so it is below each positive-sign upper bound. If there is no positive-sign index, the conclusion is vacuous.

Step 4 has no cited statement. I checked multiplication by each sign explicitly: positive coefficients preserve the upper-bound inequality, negative coefficients reverse the lower-bound inequality, and zero coefficients reduce the residual to the given b_h. Trichotomy exhausts I. An empty negative class gives the singleton B and T=0 directly from the recurrence. These elementary steps require no independent non-elementary assertion and do not merely relabel clauses with new nodes. Therefore proof_deps and citations.json are both empty. The statement dependency def-weil-field was opened: it defines the field convention, unchanged in its current blueprint_update; it is not cited as a theorem on ordered inequalities.

For boundary checks I considered I empty, each isolated sign class, zero b values, repeated equal ratios, negative lower bounds, all-positive upper bounds, equality of a lower and upper bound, and absence of either signed class. For example a=-1,b=-2 gives T=2 and zero residual; a=-1,b=2 gives T=0 and positive residual; the pair (a,b)=(1,2),(-1,-2) has equal bounds 2 and both residuals zero. The pair (1,1),(-1,-2) fails the pairwise hypothesis (-1), so is not inadvertently admitted. I also ran exact Fraction arithmetic on all systems of sizes 0--3 with coefficients from {-2,-1,0,1,2,1/2}; all 19,277 admissible systems satisfied the asserted residual and upper bounds. This is a small-case sanity check, not a replacement for the written proof.

Against delivery-errors B--E: no new statements need standalone-source/duplicate review; TeX in new proof steps uses single backslashes; inherited item statement and all hypotheses remain unchanged; no Mathlib leaf or attachment is falsely claimed; every search recorded for this session was actually run; no non-elementary black box, cited proof in place of a statement, off-unit theorem, or cycle was introduced. Each step is under 2000 characters. I checked the complete proof against its sign and finiteness hypotheses and found no statement dispute.

## Validation

The required deliver.py --no-push exited 0 and printed OK (not pushed) at f5e04cfaf5b, with server preflight passed. That includes tools/check_dag.py and tools/review_split.py on the server. No prohibited local checker, compiler, Lake, repository write or git command was run. The final report version is validated again before direct push.
