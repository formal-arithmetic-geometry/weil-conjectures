## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-finite-type-module-presentation.json`: split statement; exact mathematical statement retained, with the missing valuation-ring definition citation added. Seven proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-local-graded-flat-module-finite-presentation.json`: one new statement-only unsplit node, Stacks 053C; no Mathlib match.
- `citations.json`: ten verbatim quotation entries for the ten uses in the item's seven steps.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the item id, valuation/finite-presentation concepts, and graded/flat/local concepts. There is no declaration stating the item or the new lemma. The existing project finite-presentation/descent and free-locus results have different hypotheses. No compiler or Lake command was run.

## WANTED

None. Both needed Stacks documents are available locally.

## Audit findings and changes

The imported item is precisely More on Algebra Tag 053E(2), `lemma-flat-finite-type-valuation-ring-finite-presentation`, lines 5966--6001. It had no proof and lacked the citation defining valuation rings. I added that citation without changing its hypotheses or conclusion. The status was unsplit and its Lean audit was none; the sandbox had no previous node/report to resume.

The proof follows the polynomial graded-module route in the last sentence of 053E. Instead of making separate nodes for abstract homogenization, torsion quotients, and degree-zero localization, it constructs the finite graded module inside the module of formal polynomials explicitly. Coefficientwise torsion-freeness then avoids a torsion-quotient comparison. Evaluation at 1 is proved to have exactly the kernel `(X_0-1)N` by a finite cumulative-sum identity. Quotienting the actual presentation gives an actual finite presentation over `Q`, after which the existing 0561 node transfers it to `B`. This remains the source's graded-polynomial argument, below the unit level; no unit or chapter route changes.

New node 053C is a genuine smaller input: it concerns a *graded* finite module over a polynomial algebra over an arbitrary local ring, with every variable of positive weight. The item instead concerns an arbitrary finite module over an arbitrary finite-type valuation algebra. The homogenization, flatness verification, recovery of the original module, and scalar transfer remain in the item. I deliberately do not cite the existing local valuation presentation theorem 0GSE, whose proof depends on this item.

## Mathlib and duplicate searches

All new searches were made by `/home/ubuntu/weil-launcher-nt/msearch.py Q96 lem-trf-valuation-finite-type-module-presentation`; their actual results are retained in `searches.jsonl` and copied, with exact tool/query strings, into the applicable node. For both the item and the new node I used LeanFinder, Loogle, grep, and LeanSearch, with a second semantic phrasing. The first graded Loogle pattern was rejected for unknown `GradedModule` and is honestly recorded as unavailable; the second valid pattern returned `Module.exists_basis_of_span_of_flat`, whose source at LocalRing/Module.lean:238 already assumes finite presentation. `Module.finitePresentation_of_finite`, read at Algebra/Module/FinitePresentation.lean:118, requires Noetherianity. The module/algebra finite-presentation bridge in RingTheory/Finiteness/ModuleFinitePresentation applies to the algebra as a module over its coefficient ring and does not supply either assertion here. The graded algebra finite-generation hit supplies generators only. No returned theorem is the assertion or a one-line specialization.

I searched the whole DAG for `053C`, `flat-graded-finite-type-finite-presentation-module`, graded finite/flat/module/presentation words, and homogenization, and the whole blueprint with `blueprint_refs.py search` for `053C`, `graded polynomial`, `finitely presented graded`, and `valuation finite presentation`. No blueprint node states the new fact or item; `same_as` is empty. `blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`; the new node prepends this item to the existing via list. The current main-20261015 ancestor proof and `sk-i-curve-zero` unit were read: this is the existing semistable/flat-family input below its normal-cone branch.

## Not duplicates

- lem-trf-local-graded-flat-module-finite-presentation vs lem-trf-valuation-flat-finite-module-presentation: the latter is the local valuation-algebra theorem 0GSE, with no grading and with valuation base; it depends on the present item and cannot be cited here. The new node is the independent 053C polynomial/graded local-ring input.
- lem-trf-local-graded-flat-module-finite-presentation vs lem-sc-p1-minimal-graded-presentation-exists: the latter is over a field in two polynomial variables and only supplies a finite free surjection with a minimality property, not finite generation of its relation kernel over an arbitrary local coefficient ring.
- lem-trf-local-graded-flat-module-finite-presentation vs lem-trf-standard-graded-hilbert-function: the latter treats eventual dimensions over a field, not finite presentation over a local coefficient ring.

No existing DAG node has source tag 053C.

## What remains unfinished

Nothing needed for this one-level split. The new 053C node is intentionally left statement-only for its own worker. It is not represented as a finished proof. No external tool uses are needed: the non-Mathlib helpers and the new node are all in this item's unit; the generic definitions and torsion-freeness criteria are existing Mathlib leaves.

## Review by Q96

I read 053E(2) and its proof in `more-algebra.tex` and compared all four hypotheses: valuation ring A, finite-type algebra B, finite B-module M, and A-flatness of M. The conclusion is finite presentation over B, not over A. None was strengthened or removed. I read the full new input 053C (`lemma-flat-graded-finite-type-finite-presentation-module`, lines 5856--5909): local coefficient ring, finitely many variables with strictly positive weights, internal integer grading of L, finite generation over the polynomial ring, and flatness over the coefficient ring are exactly its hypotheses. The new node defines its grading and locality explicitly; it has no proof or proof dependencies. I read the existing 0561 (`lemma-finitely-presented-over-subring`) statement and proof in `algebra.tex` at lines 584--623 and checked the transfer is in the required direction, from finite presentation over Q to finite presentation over B.

For Step 1 I opened the valuation, finite-type-algebra and finite-module definition nodes. They supply respectively the fraction-field condition and the two finite generating lists. Locality is not falsely taken from the valuation definition: the step proves it by comparability of divisibility and the ideal of nonunits. Step 2 uses the polynomial-ring definition's universal property for the commuting actions. Its finite generation is given term by term by the displayed monomial, including the exponent `d-|alpha|`, which is nonnegative by construction. Thus no homogenization existence theorem is concealed.

For Step 3 I opened both torsion criteria. `lem-trf-flat-module-torsionfree-domain` says exactly that flatness over a domain makes every nonzero scalar injective; `lem-trf-valuation-torsionfree-flat` says exactly that torsion-freeness over a valuation ring gives flatness. The intermediate argument is coefficientwise on finite formal sums, so it uses no assertion that submodules of flat modules are flat over arbitrary rings. Step 4 uses the new 053C statement with weights all 1, nonnegative degrees (extended by zero to negative degrees), and finite generation/flatness already established. A is local by the actual argument in Step 1, not a new unstated assumption.

Step 5 has no external citation: writing `y_d=-sum_{i<=d}x_i` gives coefficients in F_d because the filtration increases, and direct multiplication yields the original kernel element, including the top coefficient since the total sum is zero. The action on M is explicitly `X_0=1, X_i=b_i`, so the resulting identification respects the Q-module action. Step 6 uses only the finite-presentation and polynomial definitions. I checked the kernel and image of the coordinate quotient map; this gives the evaluated finite relation matrix without an unstated tensor-exactness theorem. Step 7 cites the actual existing 0561 statement, which applies because Q maps surjectively to B, hence B is a finite-type Q-algebra, and M has its original B-action.

I checked B1--B10 and C1--C8 against these files: the one new statement introduces all objects and hypotheses, has ordinary single-escaped mathematical TeX, correct tag and label, no proof sketch in its statement, all definition dependencies, actual searches, and blueprint ancestry. Every citation's quote was checked as a verbatim substring of its node's statement. The proof uses statements only, not hidden proofs of cited nodes, and does not use the dependent 0GSE theorem. D1--D5 are satisfied by retaining the construction and quotient argument in the item; no new node restates its conclusion. Every step is below 2000 characters (658, 711, 320, 366, 504, 621, 420), and the elementary steps are explicit finite algebra calculations.

For E1--E7 I tested the item at M=0, B=0, n=0 (B a quotient of A), and A a field. Empty module generators produce N=0; if n=0 the homogenizing variable X_0 still exists and the argument gives a finite presentation over A before transfer. I checked the new statement for L=0, no polynomial variables (the finite-flat local-ring case), positive weights greater than 1, and shifts allowing negative module degrees. It does not assume R Noetherian or reduced. In the actual application only the positive weight 1 is needed. The cumulative-sum kernel formula includes degree zero and works when the largest coefficient vanishes. No statement dispute or source error was found. The only correction to the seeded node is its missing definition reference; the proof repairs the empty split and avoids a circular citation.
