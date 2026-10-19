# Stage-1 report: thm-zl-lefschetz-weil-identity

## Files written

- `dag/nodes/sec-zeta-weil/thm-zl-lefschetz-weil-identity.json`: statement, split; no Mathlib match. Statement unchanged, six complete proof steps, statement dependencies completed, searches recorded.
- `dag/units/sk-thm-tracetodeterminant.json`: only `realized` and `realized_by`, binding the statement and the unit's single proof step to this item.
- `citations.json`: thirteen step/node pairs, each with a verbatim quotation from the cited statement.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the read-only slopmaster2 project for the exact blueprint id and geometric and determinant terminology, and inspected `WeilConjectures/ZetaLinearAlgebra/TraceDatum.lean`, especially `TraceDatum` at line 93, `zeta` at line 151, `zeta_mul_prod_even_eq_prod_odd` at line 175 and `map_zetaSeries` at line 263. The determinant theorem is a proved abstract finite trace-datum identity. It does not by itself identify the geometric cohomology, its Frobenius operators, their degree bound, and the actual point-count zeta series, so it is not an exact attachment of this geometric item. The accompanying FrobeniusModule trace-series file describes the geometric application in its docstring but does not prove the whole item either. No master sorry declaration was counted as completed work.

## WANTED

None. The necessary sources were available locally.

## Corrections and observations

The statement was not changed. In particular its explicit assumption of the point-counting formula remains an assumption: the proof does not silently deduce the corollary's compactification admissibility from properness.

The imported first proof paragraph incorrectly assigned finiteness, invertibility and the exact vanishing interval to definitions. The current family definition explicitly says those assertions belong to the cohomological-finiteness proposition. Step 1 now cites that proposition and the existing Qbar_l scalar-extension comparison. The proper-case point-count formula itself already supplies ordinary cohomology, so no false assertion about proper coincidence is taken from the cohomology definition.

The imported proof used log/exp inverseness and logarithm additivity without citing nodes and left three elementary flags null. I use the exponential formulation of exactly the same finite-sum/per-degree-determinant route, as written in Milne 27.6. Existing lem-weil-exp-trace-determinant gives the per-degree identity, existing lem-weil-power-series-exp-hom supplies the finite product law, and the coefficient interchange is written out degree by degree. No new lemma restates the item or one of its clauses. I deliberately do not apply clause 3 of prop-trace-determinant (the whole geometric conclusion).

The item writes a rational point-count zeta series in Qbar_l[[T]]. Step 3 now identifies that with its coefficientwise image and cites compatibility with exp. The statement dependencies include the zeta, cohomology, family, formal-series, reverse-characteristic-polynomial, polynomial-to-series, coefficient-map and coefficient-field notions actually used in its statement.

## Blueprint and duplicate search

I read the fixed chapter record and the unit record, and the item's old proof and current main-20261015 statement plus the current unit statement. The imported item and current statement agree. I ran blueprint_refs searches for trace-to-determinant, formal logarithm, exponential and scalar-extension identifications, and searched all DAG nodes for the corresponding keywords and the concrete existing ids. No node was created. The existing prop-trace-determinant and unit-level sk-thm-tracetodeterminant are recorded in same_as as the characteristic-zero/general-family and Q_l versions of this factorization; this item's Qbar_l geometric specialization retains its explicit trace-formula assumption.

The route remains the unit's route: trace formula, zeta exponential, finite index interchange, per-degree log determinant in exponential form, finite product. Two outside-unit generic tools are declared in split_report.tool_uses: prop-cohomological-finiteness (the family definition expressly delegates these claims), and lem-weil-cohomology-scalar-extension-qlbar (the comparison required by the item's own coefficient convention). Neither replaces a trace-to-determinant argument. Definitions and the existing coefficient-map Mathlib leaf are notions/tools under the contract. No existing cited dependency has a path back to this item in the dependency graph checked before writing.

## Not duplicates

No new nodes; no new/existing duplicate pairs.

## Review by Q25

I checked delivery-errors B-E against the actual statements used. For the item I read Milne, Lectures on Etale Cohomology, Proposition 27.3 and Lemma 27.5, printed p. 155, the proof of Lemma 27.5 and Theorem 27.6 on p. 156, and Corollary 27.8 on p. 156; I also read Deligne Weil I (1.3)-(1.5.3), printed pp. 274-275. The blueprint sources are the old item's complete five-step proof and the unchanged current main-20261015 item and unit statements. There are no new-node sources to audit, since no new node is necessary. No SGA source is used.

Step 1 uses the statement of prop-cohomological-finiteness with E=Q_l and constant coefficients: it explicitly gives finite-dimensionality, Frobenius automorphisms, proper compact/ordinary comparison, and vanishing outside [0,2d]. Every geometric hypothesis is present. The statement of lem-weil-cohomology-scalar-extension-qlbar explicitly supplies the canonical comparison for every integer i and its compatibility with Frobenius, not just an eigenvalue claim. The basis assertion of def-weil-vector-space-scalar-extension supplies finite-dimensionality after extension; extension of a zero space and extension of the inverse map are written out. def-weil-l-adic-numbers says Q_l has characteristic zero, so its extension K also does. I corrected the original use of the family/cohomology definitions as theorems.

Step 2 takes the proper-case ordinary-cohomology trace formula directly from the statement of cor-trf-point-counting. I checked that the item explicitly assumes that formula. The corollary otherwise has compactification-admissibility hypotheses, so I wrote that we use its assumed conclusion and do not infer those hypotheses. The passage from all integer degrees to 0,...,2d uses the already proved vanishing in step 1. The geometric Frobenius convention agrees throughout.

Step 3 uses the identical exponential definitions in sk-def-zeta and def-weil-point-counts-zeta, the coefficientwise ring map defined by def-weil-coefficientwise-ring-hom-map, and the actual assertion phi(exp U)=exp(phi U) in lem-weil-exp-coefficientwise-map. Both coefficient fields are commutative Q-algebras, phi is their canonical inclusion, U has constant term zero, and the coefficient denominators are invertible. This fixes the formerly implicit change of coefficient field.

Step 4 cites no theorem: its argument compares the coefficient of each positive power of T and the zero constant coefficients, using the trace identity already established. Only the finite index sum is exchanged with coefficient extraction, so no analytic convergence or infinite-sum interchange result is hidden here. This is the sole elementary step.

Step 5 first uses the definition of a Frobenius module in def-zl-frobenius-trace-series and the exact identity log P=-A in lem-zl-log-det-identity. It then applies the complete statement of lem-weil-exp-trace-determinant, not its proof: K is characteristic zero, V_i finite-dimensional, F_i linear, and its P_u and trace series are exactly our P_i and A_i. The cited statement asserts P_i exp(A_i)=1, unit status and exp(A_i)=P_i^{-1}, and substituting A=-log P evaluates exp(-log P) for the next step. There is no diagonalizability hypothesis.

Step 6 uses the finite-family, integer-weight conclusion explicitly stated in lem-weil-power-series-exp-hom. The family is finite and every A_i has zero constant term. I checked the signs: even i contributes an inverse determinant, odd i contributes a determinant, so the final exponent is (-1)^{i+1}. No uncited logarithm law is used.

I tested d=0 with X_0=Spec F_q: N_n=1, F_0=1 and P_0=1-T, giving Z=(1-T)^{-1}. I also checked the sign on a formal two-degree example (one even and one odd space), the zero-dimensional vector-space case P=1 and A=0, and a non-semisimple unipotent 2x2 Frobenius block: trace(F^n)=2, P=(1-T)^2, so the per-degree equality still holds. The n=0 coefficient is handled separately and no division by zero occurs. These checks found no statement dispute or missing hypothesis.

All Mathlib records are literal queries actually run with the prescribed msearch command. LeanSearch and LeanFinder returned unrelated analytic zeta/trace/characteristic-polynomial facts; the corrected Loogle query returned only the coefficient-one trace identity. The first Loogle query reported an unknown LinearMap.charpolyRev identifier, which I record explicitly rather than count as evidence of absence. The second natural-language query tested the more general finite linear-algebra formulation. No search returned the geometric item or a one-line specialization proving it.

## Unfinished work

No mathematical step is left unfinished at this split level. The existing cited nodes retain their own current stage-1 states and are not modified. The sandbox is for a fresh second reader; this worker does not push a delivery.

## Preflight repair

The preliminary server review_split passed. The first full dry run reported missing unit-route reachability of sk-def-zeta and sk-prop-logdet (and an associated trace-transport route finding). I repaired this by actually using sk-def-zeta for the exponential zeta formula and lem-zl-log-det-identity for A_i=-log P_i, then using the existing exp-det lemma to evaluate exp(-log P_i). Both named unit inputs are now explicit in the calculation and in the verbatim citation file. This preserves the logarithmic route while avoiding an unsupported general log/exp inversion claim. No statement was changed and no node added.

## Second reading by Q25

- Item statement: checked hypothesis by hypothesis against `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-thm-tracetodeterminant/thm-zl-lefschetz-weil-identity.md` (node order 3222); verdict: unchanged and faithful, including the explicit assumed trace-formula clause and the \(\Qlb[[T]]\) conclusion.
- Step 1: checked against `prop-cohomological-finiteness`, `lem-weil-cohomology-scalar-extension-qlbar`, the scalar-extension definition, and `def-weil-geometric-hypotheses`; verdict: finite-dimensionality, invertibility, vanishing, and determinant transport follow under the stated smooth/proper hypotheses.
- Step 2: checked against `cor-trf-point-counting` and the item’s explicit assumption; verdict: uses the proper ordinary-cohomology conclusion and truncates only by Step 1, without inferring compactification admissibility.
- Step 3: checked against `sk-def-zeta`, `def-weil-point-counts-zeta`, the coefficientwise-map definition, and `lem-weil-exp-coefficientwise-map`; verdict: the rational series is correctly embedded coefficientwise in \(K[[T]]\), with finite-type agreement and invertible denominators stated.
- Step 4: checked coefficient by coefficient against Step 2 and the finite formal-series definitions; verdict: elementary finite-index interchange, with the constant coefficient handled explicitly.
- Step 5: checked against `def-zl-frobenius-trace-series`, `lem-zl-log-det-identity`, and `lem-weil-exp-trace-determinant`; verdict: the logarithmic identity and its exponential reciprocal are applied to the exact finite-dimensional Frobenius modules, with no semisimplicity assumption.
- Step 6: checked against `lem-weil-power-series-exp-hom`; verdict: finite integer-weight exponentiation gives the alternating determinant product with the correct even/odd signs and unit powers.
- New nodes: none; there were no new statements requiring a B1–B7 audit, and duplicate/Mathlib searches remain recorded in `searches.jsonl`.
- Source and route checks: read the Milne §§26–27 pages cited by every proof step, Deligne Weil I (1.3)–(1.5.3), the current blueprint unit, and every cited DAG statement; no SGA source, cycle, restatement node, or uncited non-elementary fact remains.
- Edge cases: checked \(d=0\), \(X_0=\operatorname{Spec}\Fq\), zero-dimensional vector spaces, empty index behavior in the exponential lemma, the \(n=0\) coefficient, and a non-semisimple unipotent Frobenius block; all give the stated identity.

Changes made during second reading:

1. Updated the item source from the superseded master blueprint file to the current `main-20261015` file and order 3222, and recorded `blueprint_snapshot: main-20261015`.
2. Added `def-weil-geometric-hypotheses` to Step 1 and to `citations.json`, because the separated finite-type hypotheses needed by cohomological finiteness are supplied by that definition.

3. Added `def-weil-geometric-hypotheses` to `proof_deps` after server preflight detected that the new Step 1 citation was not included in the dependency union.
