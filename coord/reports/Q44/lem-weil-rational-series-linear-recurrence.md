## Files written

- `dag/nodes/sec-zeta-weil/lem-weil-rational-series-linear-recurrence.json`: existing statement node, now split into four elementary steps; no Mathlib match for the whole item.
- `citations.json`: seven step/node entries, each checked against the complete, currently stored statement of its cited node.
- `report.md`: this report and the author's source review.

New nodes: 0. New Mathlib leaves: 0. The statement, statement dependencies, chapter and unit are unchanged. No unit realization file is changed: this item is a child of the unit's key proposition, not that proposition.

## Attachments

None for this item. I searched `WeilConjectures/` for the exact blueprint id/tag and for the rational-series/recurrence notions, and read `WeilConjectures/ZetaLinearAlgebra/ShiftSpan.lean` lines 139–185 and `RationalityCriterion.lean`.

`PowerSeries.coeff_coe_mul` (ShiftSpan.lean:141) states the finite convolution formula, not the recurrence. `PowerSeries.sum_coeff_mul_coeff_eq_zero` (ShiftSpan.lean:180) gives a convolution sum indexed up to `B.natDegree`, with the explicit premises `A.natDegree < n` and `B.natDegree ≤ n`. Its body contains no sorry, but it does not literally state the present lemma with the supplied arbitrary threshold, order `max(deg Q,1)` and reversed coefficients. Recovering that formulation requires the truncation, constant-term isolation and reindexing given explicitly here. I therefore do not report an exact attachment. The equivalence `PowerSeries.tfae_exists_normalized_fraction` in RationalityCriterion.lean only gives the existence of some recurrence; it does not identify the prescribed recurrence of this item. The already closed `lem-weil-rational-series-finite-shift-span` is likewise a rationality/finite-dimensionality equivalence, not this fixed-coefficient assertion.

## WANTED

WANTED: Bourbaki, *Algèbre*, Chapter IV §5, Exercise 3(a), for lem-weil-rational-series-linear-recurrence. This book is already listed as wanted in literature/LIST.md. Milne LEC p. 157 reproduces its assertion, not a proof. I obtained no document and changed no literature file. The supplied proof is marked `proof_origin.by = agent`.

## Source and imported-node findings

Read Milne, *Lectures on Étale Cohomology*, printed p. 157, proof of Lemma 27.9: part (a) quotes the equivalence between rationality and an eventual linear relation. Read the archived blueprint `master/blueprint/sec-zeta-weil/sk-prop-criterion/prop-weil-rationality-criterion.md`, final proof paragraph: comparing coefficients of QC=P yields the recurrence, with a separate Q=1 case. Read both current main-20261015 files for the unit and proposition. The current unit states rationality versus finite-dimensional shift span; the current expanded proposition still states the three conditions but gives no proof. The present coefficient calculation realizes the imported child's direction and is compatible with that route; it does not replace a unit step by another theorem.

The item is true as written. No STATEMENT-DISPUTED issue, added hypothesis, or weakened conclusion was found. The imported node had no proof, only two historical grep records, and `blueprint.same_as` was unsearched. I supplied the proof, repeated the searches through msearch.py, and set same_as to []. There is no exact equivalent blueprint node: the ancestor proposition is a strictly broader equivalence, and the neighbouring finite-shift-span node concerns a different conclusion.

## Searches and new-node audit

I searched the whole DAG by the item id and rational/recurrence/coefficient-convolution terms, and used `tools/blueprint_refs.py search` for `recurrence`, `rational power series`, and `linear relation`, plus its ancestor command. Existing definition nodes already state every ingredient: in particular the Cauchy product appears verbatim in def-weil-formal-power-series. No convolution or support-bound node is created, since these would merely repackage definitions and a finite-sum calculation.

All ten new mathlib_searches entries are actual msearch.py calls for Q44 and this item; the exact tool and query strings are retained. LeanFinder and LeanSearch were each tried with a rationality/recurrence formulation and a convolution/coefficient formulation. Loogle was tried with `PowerSeries.coeff_mul, Polynomial.coeff` (0 hits) and `PowerSeries.coeff_mul` (the Cauchy-product theorem). Grep of RingTheory/PowerSeries found coefficient-product ingredients and no occurrence of LinearRecurrence/IsSolution/rational/Rational. The degree-coefficient search found Polynomial.coeff_eq_zero_of_natDegree_lt. I read the returned types: none asserts the full fixed-coefficient recurrence. All services were available. File-specific grep calls have a wrapper display quirk (the source line number is shown in its file field); the report in the node records the actual displayed lines without treating them as another file.

## Review by Q44

I checked the item against Milne p. 157 and the archived final proof paragraph with the node's precise hypotheses in view. Milne supplies the intended rationality/recurrence implication; the four-step argument supplies what his quoted exercise omits. There are no new statements whose sources or hypotheses must be audited.

Step 1 uses the statements of def-weil-polynomial-ring and def-weil-polynomial-coefficient. They explicitly define the degree of a nonzero polynomial as its largest nonzero coefficient index, and the former identifies Q(0) with its constant coefficient. Since Q(0)=1 in the given field, Q is nonzero, so the degree definition applies. The bound on b_j is a direct consequence of that definition, not an uncited support theorem. The maximum with 1 is needed for the constant denominator and supplies d≥1.

Step 2 uses def-weil-polynomial-as-power-series for the coefficient-preserving inclusion, and def-weil-formal-power-series for precisely its displayed Cauchy-product formula. I read both statements, not their proofs or only their Mathlib names. For arbitrary n≥m, N=n+d is at least d and at least m+d. The numerator coefficient is therefore zero by the item's own hypothesis, including thresholds not introduced by the default choice of m. Terms with j>d are zero by Step 1; N≥d ensures all surviving indices are present and all N-j are nonnegative. Isolating j=0 uses b_0=1. No result about inverses, rational functions, convergence, or unique normalized fractions is used.

Step 3 cites def-weil-eventual-linear-recurrence, whose statement gives exactly c_(n+d)+sum a_i c_(n+i)=0 for every n≥m. I checked the reversal explicitly: j=d-i sends j=1 to i=d-1 and j=d to i=0, and n+d-j=n+i. Finite-sum reversal is the entire argument in this step; it introduces no linear-algebra assertion. It yields the coefficients specified in the item rather than arbitrary coefficients from the existence theorem in Lean.

Step 4 cites the degree/coefficient statements already opened. For nonzero P, N≥deg P+1+d implies N>deg P. For P=0, every coefficient is zero and the proof needs no degree convention for the zero polynomial. For Q=1, its nonconstant coefficients are all zero, so padding to d=1 yields a_0=0 and exactly c_(n+1)=0. The same reasoning covers P=0,m=0 and does not divide by a coefficient that could vanish.

I tested the boundary calculations over Q with P=0,Q=1,m=0; P=T²,Q=1,m=2; P=1,Q=1−T,m=0; P=T,Q=1−T³,m=0; and P=1+2T+3T³,Q=1−2T²,m=2. I also tested characteristic 2 with P=1,Q=1+T²,m=0. A finite coefficient-generation calculation verified the supplied recurrence through degree 19 in all six cases. These checks cover the padded constant denominator, a minimal valid threshold, the zero numerator, a denominator with internal zero coefficients, and a field of positive characteristic; the general proof is the coefficient calculation above.

Against delivery-errors B–E: no new node duplicates the item or one of its clauses, and no unproved argument is hidden in a new statement; all notions are already defined by the six statement dependencies; every cited step/node pair has a verbatim quote; no step applies a result with missing hypotheses; every elementary step spells out its finite calculation. No Stacks tag is needed for this definitional coefficient argument. Only existing definition leaves occur in proof_deps, so no cycle or off-unit proof-tool use is introduced. I corrected no mathematical statement. The work completed here is the previously missing proof and search/reference metadata.

## Unfinished work

None in the split. Independent second reading and delivery remain assigned to the next worker. This worker runs only the no-push dry run and leaves the sandbox for that reader.

## Second reading by Q44

- Item statement: checked against Milne, *Lectures on Étale Cohomology*, Ch. II §27, proof of Lemma 27.9, p. 157, and the archived/current rationality-criterion blueprint; every field, polynomial, normalization, threshold, and recurrence clause agrees, including $P=0$ and $Q=1$.
- Step 1: checked against the complete statements of [def-weil-polynomial-ring] and [def-weil-polynomial-coefficient]; the nonzero denominator and support bound $b_j=0$ for $j>d$ follow directly, so the elementary verdict is sound.
- Step 2: checked against [def-weil-polynomial-as-power-series] and [def-weil-formal-power-series]; coefficient preservation, the finite Cauchy sum, the threshold $N=n+d$, and truncation at $d$ supply exactly the displayed identity, with no missing hypothesis.
- Step 3: checked against [def-weil-eventual-linear-recurrence]; the finite reindexing $i=d-j$ gives the stated coefficient order and all indices, so the elementary verdict is sound.
- Step 4: checked against the complete polynomial degree/coefficient statements; the $P=0$, nonzero $P$, and $Q=1$ boundary cases are valid and preserve $d\geq1$.
- New nodes: none; therefore B1--B7 and duplicate/existing-node checks are vacuous. All five proof dependencies are existing definition/mathlib leaves, and each citation quote matches its node verbatim.
- Changes made: none to the mathematics or node metadata. Added this second-reading audit only; the split already contains the required proof, searches, blueprint ancestry, and edge-case checks.
