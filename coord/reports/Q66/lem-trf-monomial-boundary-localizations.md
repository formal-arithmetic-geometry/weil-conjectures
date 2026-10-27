# Stage-1 report: lem-trf-monomial-boundary-localizations

## Files written

- dag/nodes/sec-trace-formula/lem-trf-monomial-boundary-localizations.json: item, statement, split into ten proof steps; no Mathlib match for the bundled chart assertion.
- citations.json: eight verbatim statement quotations, covering every step/node citation.
- report.md: this report. searches.jsonl was written by the required search command.

New nodes: 0. New Mathlib leaves: 0. The existing DAG supplies every non-elementary input. No unit realization file is applicable: this auxiliary node is not its unit's key statement.

## Attachments

None for this item. Searches in lean/WeilConjectures for the item tag, monomial/facet combinations, and boundary/valuation terminology did not find a declaration stating all its clauses. The existing project declaration IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton belongs to the already attached lem-sc-principal-ideal-dvr; it only supplies the general DVR recognition input, not the item.

## WANTED

None. ILO VI 1.6 and all required Stacks algebra sources are present and were read. This proof is marked agent-written: ILO gives the chart models, not this arbitrary-domain chart theorem.

## Corrections and scope

The statement and statement dependencies are unchanged. There is no statement dispute. The original item was unsplit, with no proof. The current parent lem-trf-complete-toric-facet-valuations already delegates its boundary-localization clause to this item; citing that parent here would be circular, and it is not used.

The proof makes both denominator arguments explicit: Step 2 chooses a finite maximum of integer bounds, and Step 4 proves the fraction identity by the equality q+d+mb_i=c+ma_i in P and its multiplicative image. It does not assume a monomial basis for R, normality of R, a Dedekind hypothesis on R, or independence of monomial images. The only chart algebra assumed is exactly the statement's multiplicativity, nonvanishing, primality and membership equivalence.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for monomial, facet, principal maximal ideal, and the relevant DVR/localization facts found existing supporting nodes, which are reused. lem-sc-principal-ideal-dvr is the exact recognition theorem; lem-sc-normal-dim1-dvr would require an unnecessary normality hypothesis. The parent and other toric nodes are not substitutes for this item's proof. The item remains distinct from the general principal-ideal recognition and dimension nodes because it constructs the generator and proves the monomial factorization and boundary exhaustion.

## Search evidence

The five new searches in searches.jsonl were executed through batch2/msearch.py for Q66 and this item: two LeanFinder phrasings, Loogle, Mathlib grep, and LeanSearch. All services returned successfully. I read their results. The first semantic search finds the general DVR TFAE and the Dedekind localization theorem; the former is already the recognition input, and the latter has a stronger hypothesis on the ambient ring and gives no explicit monomial formula. The second finds projective-spectrum graded localization declarations and the maximal-ideal membership rule, not facet exhaustion. LeanSearch finds localization definitions, not the chart theorem. The four grep hits are univariate rational-function/polynomial valuation formulas; I read AsPolynomial.lean around 317 and IsTrivialOn.lean around 41, and they assume an already given valuation trivial on constants. None constructs the valuations or boundary primes here. The inherited 2026-10-22 search records are retained, including its unavailable LeanSearch result; new searches do not silently replace the historical evidence.

## Review by Q66

I read coord/brief-stage1.md, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, roles/worker.md, tools/README.md, and delivery-errors.md B--E (both copies). The current chapter/unit and ancestor sources were read from literature/blueprint/latest, whose COMMITS.txt points to main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345. The local chapter/unit records are older than that snapshot, but this is a purely algebraic auxiliary item in the existing ancestry and does not replace or change a unit step. I read the parent statement and its assembly proof to check the precise input this item must supply.

For the item's source I read ILO Expose VI, printed pp. 69--70 (PDF pages 75--76), especially 1.4 and 1.6(i)--(ii). They motivate the complete toric charts and do not assert this refinement. I also read Stacks algebra.tex: 00PD, label lemma-characterize-dvr, including the nonzero principal maximal ideal criterion and valuation construction; 00FN, label lemma-Noetherian-permanence, the localization clause; 00KF, label definition-height; and 00E3, label lemma-spec-localization. The ancillary dimension proposition 00KQ named in the item source was read, but no use of its dimension-ideal-of-definition equivalence is needed: existing DVR dimension and localization-height nodes suffice.

I opened the statement of every cited node, rather than borrowing its proof. Step 1 uses only the empty intersection and sharpness definitions. Step 2 uses finiteness and strictly positive integer values to write the bound, including the case where there are no other facets; it proves nonzero and distinct primes from the hypotheses rather than citing a clause of the parent. Step 3 cites def-weil-pbc-localization-at-prime for precisely its fractions and maximal ideal pR_p; the injectivity/domain and fraction-field claims are checked directly from its fraction equivalence and the domain hypothesis. Step 4 writes an actual inverse for u_q and cross multiplies in P, so it does not use an unproved extension of z to G. Step 5 is the elementary generator argument for the ideal extension; it uses m>=1 only on its stated positive-normal generators.

Step 6 cites lem-weil-pbc-localization-noetherian, whose statement applies to arbitrary multiplicative-set localizations of Noetherian rings; S is the complement of a proper prime, and the fraction construction satisfies its three displayed localization conditions. It then cites lem-sc-principal-ideal-dvr, whose statement is exactly the criterion needed. Domain and locality were established in Step 3, Noetherianity just established, and nonzero generator and ideal equality were established in Steps 3 and 5. The latter node is already Lean-closed, and I read the project theorem at WeilConjectures/Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean:26--33; it explicitly derives the non-field condition. The definition node def-sc-discrete-valuation-ring gives the meaning of uniformizer and the value group Z.

Step 7 uses def-sc-discrete-valuation-ring for the normalized valuation meaning, and lem-sc-dvr-valuation-arithmetic for its stated multiplication and positive-power identities. Unit value zero is proved with the inverse and nonnegative values; m=0 is handled separately. It does not take the valuation formula from the proof of any cited node. Step 8 uses exactly the statement dim A_i=1 of lem-sc-dvr-dimension-one and the full chain supremum statement of lem-weil-pbc-localization-dimension-chains-below-prime; the forbidden intermediate prime would give length two. Step 9 is the explicit elementary finite-product/primality proof, and Step 10 uses only the stipulated definition of height one and the witnesses already constructed. There is one citation entry per cited node in each of Steps 3, 6, 7 and 8, with its verbatim statement.

These supporting nodes are existing Mathlib leaves or, for principal-ideal DVR recognition, Lean-closed. Thus they are generic algebra tools, require no new off-route theorem and do not replace the unit's geometric route. No new node needed a separate source or search. Every proof step is shorter than 2000 characters; none hides a comparison lemma or an identification deferred as standard.

I tested the small cases explicitly. If I is empty then P=G and sharpness gives zero, with only the unit monomial. If I has one element, sharpness forces ker(nu_i)=0; no positivity bound on another facet is needed and f_i may be zero. For q=0, m=0 and the formula yields 1 with a unit numerator/denominator. For a q on the i-th face, the same m=0 case gives a unit. For G=Z^2, P=N^2 and R=k[x,y], the witnesses (0,1) and (1,0) give the expected x and y uniformizers; an arbitrary e_i with negative other coordinate is repaired by precisely the chosen bound. A rank-two sharp non-free saturated monoid is also allowed: no step assumes P is a free monoid, only the stated lattice half-space equality. If R were a field with a nonempty I, the hypotheses would already fail because the constructed nonzero positive-normal monomial cannot belong to a proper prime. The exhaustion proof does not assume Q monomial and does not infer a sum's valuation from its monomial terms.

Against B--E specifically: B has no new nodes, all notions are introduced and existing dependencies retained, search queries are the executed queries, and all citations use single TeX escapes at the semantic JSON-string level. C is discharged by reading and quoting actual supporting statements and writing the elementary fraction/product arguments. D is an explicit construction and argument with no new restatement nodes. E is checked by the hypothesis and small-case analysis above; no assumption is added or silently weakened.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled. Required server dry run and direct delivery follow this report; their results are reported by the delivery command.
