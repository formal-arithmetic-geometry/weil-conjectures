# Worker report: lem-trf-shift-filtered-matrix-inverse

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-shift-filtered-matrix-inverse.json`: statement, split; no exact Mathlib match. Six explicit proof steps.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch results, retained without alteration.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. Two existing Mathlib theorem leaves are reused: `lem-weil-pbc-power-series-local-ring` and `lem-weil-pbc-matrix-adjugate-identity`. Existing definition leaves give the coefficientwise Cauchy product and the Leibniz determinant formula.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, the item id, shifted/filtered matrix terminology and cofactor terminology found no declaration stating the entire item. Existing Mathlib scalar inverse and block-triangular inverse results do not state the coefficient-shift estimate.

## WANTED

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero, Invent. Math. 128 (1997), Lemma 9.12 and (9.13), printed pp.280--281, as a locally archived document, for the contextual origin of lem-trf-shift-filtered-matrix-inverse. The imported source links the journal PDF, but this delivery does not claim to have read that absent local document or to derive its support calculation from it. No missing source is needed to verify the explicit agent-written algebra below.

## What changed and what was wrong

The statement and its statement dependencies are unchanged. The item was a statement-only algebra prerequisite of the already-reviewed `lem-trf-exact-block-coefficient-projection`, used in its step 6. The sandbox initially had only launcher brief markers and no split or report; no previous proof or completed delivery was discarded.

The historical blueprint ancestor is `lem-trf-local-term-locality`, not a blueprint statement of the present matrix lemma. I read the current `literature/blueprint/latest/` statement and proof and the recorded unit/chapter. The current blueprint does not itself state a shifted formal-matrix support lemma. I retained the ancestry and the existing, specified `from.place`; no unit or chapter route is replaced. ILO VIII 2.3.11--2.3.13, printed pp.93--94 (PDF pp.99--100), discusses desingularization algorithms and their functoriality. It does not prove this algebra estimate. Thus `proof_origin.by` is explicitly `agent`. No SGA source is used.

The algebra argument is as follows. Embed exponent tuples in the additive lexicographic group by theta(delta,v)=(|delta|+sum(v),delta,v). In an (i,j) adjugate entry, the cofactor deletes row j and column i. Each nonzero coefficient summand matches all remaining rows to all remaining columns. Adding the entry hypotheses gives theta(delta,U-u_j)>=theta(0,U-u_i), where U is the sum of all weights. Add theta(0,u_i+u_j) and cancel theta(0,U), obtaining the correct theta(delta,u_i)>=theta(0,u_j). Finally multiplying by any scalar formal series only adds a nonnegative W exponent. This proves the support of det(A)^(-1) adj(A), the unique two-sided inverse by the existing adjugate identity and formal-series unit criterion. There is no appeal to a geometric series, convergence, distinct weights, or a positivity assertion about differences in natural numbers.

## Searches and existing nodes

I searched the whole DAG for adjugates, cofactors, units characterized by constant coefficients and coefficient convolution, then opened the actual existing statements. Blueprint searches by `adjugate`, `coefficient support`, `degree lexicographic`, `power series` and cofactor/shifted-matrix terminology gave no blueprint equivalent of this item. The item already had Q21 search records, which are preserved; six actual Q81 searches are appended from `searches.jsonl`. All four requested tools were used; a second semantic phrasing was run before concluding absence. All services returned successfully.

The first phrasing returns scalar `MvPowerSeries.inv`, `coeff_inv` and `invOfUnit`, plus a polynomial-matrix support inclusion. The second returns `Matrix.blockTriangular_inv_of_blockTriangular` and its block consequences. I read the source at `Mathlib/LinearAlgebra/Matrix/Block.lean:423`, `Matrix/NonsingularInverse.lean:170--217`, `Matrix/Adjugate.lean:264--269,367--370`, and `RingTheory/MvPowerSeries/Inverse.lean:131--155,197--241`. Scalar inversion does not state row/column weight bounds; block triangularity controls zero entries, not positive-degree coefficients within entries. The adjugate formula supplies a tool, not the whole assertion.

## Not duplicates

No new node pairs: no new nodes are created. The existing adjugate identity and power-series unit theorem are cited directly. The order translation, the finite expansion witness, weight cancellation, scalar convolution and inverse uniqueness are elementary steps rather than new DAG nodes. No node restates the item's conclusion or one of its clauses.

## Review by Q81

I checked the split against sections B--E of delivery-errors with the statements open. The item introduces its field, matrix, series ring, determinant and exact order. Its nonnegative dimensions and determinant assumption are sufficient; no characteristic, Noetherian, completeness, distinct-weight or nonempty-index hypothesis is added. The coefficient proof is finite in every fixed multi-index, so it makes no analytic or inverse-limit claim. There are no new statements requiring a separate source or duplicate comparison.

Step 1 is the coordinate proof of translation invariance and closure under finite addition in lexicographic Z^(1+m+n). At the first coordinate where any lex-nonnegative summand is nonzero, its value is positive and no other summand is negative there. This justifies addition and cancellation even when the original weight differences have negative coordinates. No external ordering theorem is hidden.

Step 2 uses the field definition only to invert the nonzero constant coefficient; a field is local with maximal ideal zero because an ideal containing a nonzero element contains its inverse times that element, hence 1. Clause (a) of `lem-weil-pbc-power-series-local-ring` says exactly that a series is a unit iff its constant coefficient is a unit. This applies to D=det A in the finitely many variables of the statement, including zero variables. `lem-weil-pbc-matrix-adjugate-identity` states both products with the adjugate are det(A) times identity. Its commutative-ring hypothesis holds for R by the power-series definition. Multiplying these identities by the scalar inverse gives both inverse equations. The displayed calculation B'=B'(AB)=(B'A)B proves uniqueness without an additional matrix-inverse result. I checked the unit and adjugate declarations against the pinned Mathlib source; the adjugate source is also the formula used in Stacks Tag 07DQ, label lemma-matrix-left-inverse. I do not miscite that Stacks lemma as a shifted-support result.

Step 3 uses the **statement**, not the proof, of the adjugate node: its entry (i,j) deletes row j and column i. The determinant definition supplies exactly a finite signed permutation sum; the series definition supplies exactly the finite convolution formula. Iterating that formula over finitely many factors yields the displayed coefficient summands. A nonzero finite sum has a nonzero summand and a nonzero product has no zero factor. These are the two elementary inferences used; there is no claim that a sum of nonzero summands cannot cancel. For r=1 the cofactor determinant is the empty determinant and has only coefficient delta=0.

Step 4 applies precisely the original entry hypothesis to each nonzero factor selected in step 3. The row and column index sets differ by deleting j and i respectively, so summing cancels to the claimed (u_i,u_j), not its reverse. I explicitly wrote the addition/cancellation calculation. It is two elementary lines from step 1 and introduces no separate filtration-comparison theorem.

Step 5 uses the finite scalar-product convolution from the series definition. A nonzero output coefficient selects eta in the cofactor support and epsilon>=0 from the scalar inverse; theta(epsilon,0)>=0 was proved in step 1. Adding gives exactly the requested bound. It requires no extra theorem restricting the support of the inverse scalar series.

Step 6 checks all degenerate cases. The empty matrix has determinant 1 and no entries. With m=0, there are only scalar coefficients and the cancellation proves the familiar weight-triangular support assertion. With n=0, the weight condition is automatic. Repeated weights are allowed because every inequality was weak and no choice ordering the weights was made. For r=1, the scalar inverse has arbitrary nonnegative W support and both weights in its only entry agree. As a concrete orientation check, for m=n=1 and weights u_1=0,u_2=1, A=[[1,W],[1,1]] meets the hypotheses and its inverse is (1-W)^(-1)[[1,-W],[-1,1]]: the upper-right entry still has no constant term, as the statement requires. For equal total-degree weights in several coordinates, the full lexicographic theta coordinates, not just the total degree, remain in the cancellation, so ties are covered.

Every cited step/node pair has its exact statement in `citations.json`. Every proof step is shorter than 2000 characters; I checked that none hides a non-elementary comparison lemma. The only non-elementary step cites the two existing theorem leaves it uses; all remaining steps write out finite sums, definitions and ordered-coordinate arithmetic. I did not create elementary nodes, move the conclusion into a child node, alter any other node, write Lean, compile, run a local preflight, or run git in the shared repository.

## Unfinished work

None in this stage-1 split. There are no new queued prerequisites. The delivery tool's server dry run is the required mechanical validation; its final result is reported separately by the direct-delivery command.
