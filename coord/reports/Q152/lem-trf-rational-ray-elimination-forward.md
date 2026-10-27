# Stage-1 report: lem-trf-rational-ray-elimination-forward

## Files written

- dag/nodes/sec-trace-formula/lem-trf-rational-ray-elimination-forward.json: existing statement, now split into four elementary steps; no exact Mathlib match.
- citations.json: empty list, because the proof cites no nodes.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, rational ray/cone, Fourier--Motzkin and inequality-elimination terminology; no declaration of this assertion was found. No Lean file was written or compiled.

## WANTED

None for this elementary assertion. The parent's Kato proof request is not needed here.

## Findings and source

The existing statement is correct and unchanged, including infinite-dimensional V and all empty-index cases. There was no proof to preserve in the sandbox and no released repair note for this item. Existing searches, source and ancestry are retained. I read lem-trf-rational-cone-dual-finite in full, particularly its generator-induction step 3 and its source qualification. The ILO PDF, Expose VIII Remark 3.1.29 on printed p. 103 (PDF page 109), discusses combinatorial desingularization and toric varieties; it does not prove this elementary elimination assertion. The node therefore correctly records an agent-written proof. No Stacks theorem or SGA source is used.

The inherited unit is sk-i-curve-zero. I read the chapter and unit records and the current main-20261015 blueprint ancestor lem-trf-local-term-locality. The ancestor has no rational-cone argument: ancestry is historical, as the existing blueprint.from.place already says. I have not invented a cone clause in that blueprint. Whole-blueprint searches for rational and elimination and DAG searches for rational ray/signed elimination/Fourier--Motzkin found no equivalent blueprint statement. The parent finite half-space theorem is more general in aim but uses this item, so citing it would be circular; the witness sibling proves the reverse direction, not this one.

The logged Q152 searches cover LeanFinder twice with different phrasings, LeanSearch, Loogle and source grep. I read their returned hits and the FourierMotzkin tactic definitions (lines 145--235). Arithmetic and tactic hits supply no one-line specialization giving the finite family and all its clauses; the implication is instead the explicit calculation in Steps 3--4. The inherited 2026-10-22 search history is also retained without claiming to have rerun it.

## Review by Q152

I checked B1--B10 against the statement and source: no new nodes or restated clauses were introduced; the statement introduces every object; the original field-definition statement dependency remains; source and TeX are preserved; no Mathlib leaf is claimed. The proof uses only elementary finite-set enumeration, the defining identities of rational linear forms, distributivity and the elementary rule that a sum or product of nonnegative rationals is nonnegative.

For Step 1 I checked the three subsets really lie in finite I and wrote out the disjoint-union index and its cardinality, retaining multiplicities rather than confusing a family with a set. For Step 2 I expanded additivity and scalar compatibility for each pair form: a_i and a_j are rational numbers, so all resulting coefficients remain rational. For Step 3 I checked the zero-sign substitution and the positive-sign use of t >= 0; this hypothesis is genuinely necessary for that block. For Step 4 I checked a_i > 0 and -a_j > 0, the order of the two residuals, and cancellation of the t terms. The expression is a_i f_j(x)-a_j f_i(x), with exactly the sign in the statement. Every proof uses list is empty, so there is no cited-node claim requiring a quote; citations.json is [] (C1/C4).

Against C2--C8 and D1--D5, these are short elementary calculations, not a hidden elimination theorem or a new node that merely restates the item. There is no induction, converse, choice of witness, division, existence theorem, cycle, off-unit black box or imported proof used silently. Each step is under 2000 characters. Against E1--E7 I checked no finite-dimensionality or nonzero-vector assumption was introduced. If I is empty the family is empty. If either signed class is empty there are no pair inequalities. If v=0 every a_i=0 and the conclusion is exactly the residual hypothesis. If V=0 all forms and evaluations are zero. Zero forms lie in I_0; repeated forms remain separate indices and cause no issue. For a numeric opposite-sign check, a_i=2, a_j=-3, t=1, f_i(x)=3, f_j(x)=-2 gives residuals 1,1 and the pair value 5, equal to 2*1+3*1. The same identity proves equality cases as well. No statement correction was necessary.

## Not duplicates

No new nodes were created.

## Unfinished work

None in the mathematical split. Required server dry run and direct delivery follow this report.
