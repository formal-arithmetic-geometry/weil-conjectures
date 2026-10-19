## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fitting-ideal-minor-inclusions.json`: statement, split into four proof steps; Mathlib searches do not find the three determinantal-ideal inclusions themselves. Statement, source, ancestry and unit retained.
- `dag/nodes/sec-trace-formula/lem-trf-determinant-column-expansion.json`: statement, new Mathlib leaf `Matrix.det_succ_column`, `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:787` (formula and proof read through line 793).
- `citations.json`: exact statement excerpts for all three step/node citation pairs.
- `searches.jsonl`: search-command log, retained as produced. The existing item's earlier searches are retained; this attempt appends its own actual searches and records the new leaf's four searches verbatim.

## Attachments

None for this item. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, Fitting/minor-ideal terminology, and Laplace/column-expansion terminology found no project declaration stating the item or the proposed new leaf. The existing node `lem-weil-pbc-cauchy-binet` already has a closed `Matrix.cauchy_binet` attachment in the shared DAG, and is cited without alteration. Its recorded module is not present in the supplied read-only source checkout; this delivery relies on the existing node's full statement and closed audit, rather than inventing a fresh attachment.

## WANTED

None. The relevant Stacks sources and the pinned Mathlib formula are available locally.

## Corrections and observations

No statement dispute or statement correction. Stacks Tag 07Z7 (`more-algebra.tex`, `lemma-ideals-generated-by-minors`, lines 1325 onward) states the three claims in row/left-multiplication form; the item's column/right-multiplication form is the transposed version and is proved directly here. All conventions, including empty matrices, remain unchanged.

Stacks omits the proof and gives only the instruction to expand along a row or column. Thus `proof_origin.by` is `agent`: the actual descent argument, quantified induction on the number of appended columns, and restricted-product Cauchy–Binet calculation are written out. No claim that the source contains these steps is made. This fixes the lack of any proof steps in the imported item, without merely creating nodes for its own clauses.

The item is not its unit's key node, so no unit record is edited. I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current `main-20261015` ancestor statement/proof and unit statement. The pre-existing ancestry runs through the first-Fitting definition and nodal-family geometry. The nearest ancestor has no literal Fitting clause. This algebra split neither changes that ancestry nor replaces the contracting-correspondence route. Cauchy–Binet is declared as a generic off-unit tool in `split_report.tool_uses`; the other input is the new Mathlib leaf.

## Unfinished work

None within this one-level split. The new node is a Mathlib leaf and carries no proof or proof dependencies. No Lean was written or compiled, and no live file was changed.

## Not duplicates

lem-trf-determinant-column-expansion vs lem-trf-fitting-ideal-minor-inclusions: the shared Tag 07Z7 is a source hint; the new node states an equality expressing a single square determinant by its cofactors, while the item states inclusions of ideals of minors for arbitrary rectangular matrices. The equality is a smaller reusable Mathlib theorem, not any clause of the item.

lem-trf-determinant-column-expansion vs lem-trf-fitting-ideal-independence-base-change: both source references mention Tag 07Z7, but the latter is presentation independence and arbitrary ring base change of Fitting ideals of finite modules; it does not state a cofactor expansion, and the new node involves no module presentation or base change.

The full DAG was searched for Tag 07Z7, its label, Laplace/cofactor expansion, `det_succ_column`, and `det_succ_row`. `lem-weil-pbc-cauchy-binet` and `lem-sc-finite-free-complex-homology-upper-semicontinuous` mention expansion in proofs, but neither statement gives the single-column cofactor formula. The full imported blueprint was searched with `tools/blueprint_refs.py search` for `minor`, `minors`, `determinant`, `Laplace`, `Cauchy`, `cofactor`, `07Z7`, and `column expansion`; there is no blueprint node with the new statement. Existing matrix, submatrix and determinant definition leaves are reused.

## Review by Q68

I read Stacks Tag 07Z7 (`lemma-ideals-generated-by-minors`) in `literature/stacks-project/more-algebra.tex` and checked its tag against `tags/tags`. The ring is commutative, the matrices and indices are finite, and no field, domain, flatness, finite-presentation or Noetherian hypothesis is introduced. The source uses appended rows and left multiplication, whereas the item uses appended columns and right multiplication; the explicit arguments establish exactly the latter forms. I also read Stacks Tag 0F0K (`algebra.tex`, `item-cauchy-binet`) and the complete existing Cauchy–Binet node statement. For the new leaf I read the source's expansion hint and the exact Mathlib theorem at lines 787–793. Its `CommRing R`, `Fin (m+1)` indices, arbitrary column index and increasing `Fin.succAbove` deletions are precisely the new statement. The zero-size cofactor convention agrees with `def-weil-pbc-matrix-determinant`, whose full Leibniz definition I read, and with Mathlib's `det_fin_zero` at 797–798.

In Step 1 no result is imported: ideal closure and the meaning of an ideal generated by a set justify checking generators. The target is the whole ring when r=0, and nonexistent source minors generate the zero ideal. In Step 2 the cited column-expansion statement gives exactly the displayed determinant decomposition needed: deleting one selected row and column leaves an r-minor of the same original matrix. Ideal closure then proves the inclusion. In Step 3 the same formula is applied only in the branch where the final added column is actually selected. The other branch uses the previously proved descending-size inclusion for D. The induction claim is quantified over all matrices and dimensions at each d, its base is d=0, and its step uses the induction hypothesis only for the prefix with d new columns. Consequently the induction is not circular and uses no unstated comparison theorem. The cofactors use the remaining selected rows of D; they are not implicitly identified with an unrelated matrix of different row size.

In Step 4 I checked the full statement of `lem-weil-pbc-cauchy-binet`: it accepts any commutative ring, an r-by-n matrix and an n-by-r matrix, sums over r-element subsets in increasing order, and returns exactly the formula used. The equality between the chosen product submatrix and A_I C_J is proved entry by entry in the step; it is not asserted as an uncited transport. The first determinant in every summand is a generator of J_r(A) and the second is simply a ring coefficient. These are exactly the two cited statements' contents, and the quotes in `citations.json` are literal parts of their statements. No new node is merely a definition cited as a theorem; neither a proof-internal construction nor a stronger conclusion is borrowed from an existing node.

I tested the new formula for m=0: the sum has one term, M_00 times the empty determinant 1, hence equals the 1-by-1 determinant. For m=1 it gives ad-bc in either column, including the negative sign for deleting row 0 and column 1. It remains valid in characteristic 2, rings with zero divisors, and the zero ring. For the item I checked r=0; p=0 or n=0; d=0; r beyond a matrix dimension; and the induction branches for a minor that uses or omits the last new column. In particular r>n forces r+d>n+d, so no appended-column minor can contradict a zero target ideal. If r exceeds p or n in the product clause, both relevant matrices have the same dimensions, so both ideals are zero. No division by a determinant or integer occurs.

Against delivery-errors B–E: the new node is self-contained, statement-only, names all three existing definition dependencies, uses single-escaped TeX and the verified Stacks tag/label, and records only search-command queries actually run. Two genuinely different phrasings were used before finding no determinantal-ideal match; returned matrix-ideal monotonicity results concern a different construction. The Laplace query returned an exact Mathlib match, and both its declaration and line were read. The shared-tag distinctions are recorded above. There is no dependence on the parent Fitting-independence node, hence no cycle back through the item. Each proof citation was checked against its statement. All non-elementary inputs are cited nodes. The four steps are each below 2000 characters; the induction and the product-submatrix equality hide no additional comparison lemma. No mathematical correction was required after this check.
