# Stage-1 worker report: thm-trf-grothendieck-lefschetz-finite-ring

Q67, 2026-10-17. This repairs an earlier sandbox attempt and leaves a first-worker handoff for a fresh second reader. No push is made.

## Files written

- `dag/nodes/sec-trace-formula/thm-trf-grothendieck-lefschetz-finite-ring.json`: existing statement node split into seven steps. Mathlib verdict: no matching geometric trace formula. Zero new nodes, zero Mathlib leaves.
- `dag/units/sk-thm-trace-formula.json`: only `realized` and `realized_by` filled. The item realizes the statement; the existing coefficient-morphism trace formula carries all four reduction steps, and `d-lines` supplies the charts explicitly used in the affine-line step.
- `citations.json`: all 16 step/node pairs, with verbatim excerpts from the current node statements.
- `report.md`: this report. Other preparation and search-log files already in the sandbox are not project files.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source for the exact blueprint id, Grothendieck/Lefschetz, and the unit's declaration name. `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_trace_stalkFrobenius`, at `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Main.lean:111`, has `sorry` at line 126. It states only the fixed-point form and assumes dualizability and finite indexing rather than proving those assertions. It is not an attachment. The adjacent additivity theorem is also sorried. Upstream master is reference material only; no Lean was written or compiled.

## WANTED

None. The current main-20261015 theorem statement, proof, and unit, together with the current DAG statements, suffice for this one-level split. This is an agent proof following the blueprint, not a claim of an independently sourced Stacks proof of the full formula.

## What was wrong and what changed

The imported argument compressed the iterate induction, local stalk identification, closed-point regrouping, and finiteness into a paragraph. The split writes out the induction and each operator identification, then explains the cardinality and divisibility of the groups in the point sum. It applies the existing, strictly more general coefficient-morphism trace formula, which already has the unit's finite-scheme, affine-line, affine-induction, and localization route. No new node restates any clause of the item.

The imported statement dependency `def-weil-weil-sheaf-complex` describes a different field-stage category. It is replaced by `def-trf-strict-weil-complex`, which explicitly defines the finite-stage category of pairs, not a derived category of Weil sheaves. The trace and Frobenius-operator definitions and the existing closed-point-degree definition are added as statement dependencies for the displayed notation. The statement's mathematical content is unchanged. Its sole text edit inserts whitespace after the legitimate TeX double-backslash row separator in substack, avoiding the parser's interpretation of the next d_x as an escaped command. Deleting whitespace from the old and new strings gives the identical string.

The earlier sandbox attempted to derive canonical local transport using the absolute-Frobenius factorization. The current `def-trf-frobenius-operators` explicitly defines that transport as kappa composed with the fixed-point pullback identification. Step 4 now uses this statement directly, removing the unnecessary factorization and absolute-Frobenius-site premises and their citation certificates. It retains the specified maps, with no arbitrary identification of stalk objects. The corresponding two unused off-unit tool declarations are removed.

All imported source, import flags, and blueprint metadata are preserved apart from filling `same_as`. The item is `split`, not `reviewed`. There is no STATEMENT-DISPUTED assertion: its mathematical statement agrees with the current theorem text. The existing `def-trf-categorical-trace` distinguishes perfect complexes from complexes with merely finite cohomology; this proof uses the coefficient-morphism theorem's explicit perfectness assertion and makes no identification of those two categories.

## Mathlib and blueprint searches

The item's own Lean state is none, so its mathematical statement was searched. I reran through the required msearch command: LeanFinder with both recorded formulations, Loogle with the quoted Frobenius-name query, LeanSearch with the compact-support/stalk-trace formulation, and both recorded Mathlib grep patterns. The six retained records have exactly the executed tool and query text. LeanFinder returned finite-field algebra traces and etale-algebra facts; LeanSearch returned linear-map and field-extension trace formulas; Loogle returned ordinary Frobenius ring maps and their iterates; grep returned the model-theoretic Lefschetz principle and a local notation for a Frobenius equivalence. Their types do not concern sheaf cohomology, so none is an exact match or one-line specialization. The older malformed Loogle query is removed from the delivery record; it was not evidence of absence. No service-unavailable response is presented as a negative result.

I searched the whole DAG by Grothendieck/Lefschetz, coefficient-morphism trace formula, and the Lean declaration name, and ran `tools/blueprint_refs.py search 'Grothendieck'` and the ancestor command. The existing coefficient-morphism theorem generalizes the rational-point identity; the E and Qbar trace formulas and upstream batch assumption use other coefficient categories. They are not equivalent statements of this finite-ring theorem. Thus `same_as` is empty. The ancestor is the item itself. No new node was necessary.

## Not duplicates

There are no new nodes, hence no new/existing tag pairs.

## Review by Q67

I read the main-20261015 theorem's `.md` and `.proof.md`, the current unit `_section.md`, the chapter and unit records, and SETUP's three-level route requirement. The theorem retains separated finite-type X_0, the same finite coefficient ring A, strict finite-Tor Weil structure, the explicit etale-origin witness, and the exceptional-admissibility/compactification hypotheses. Both formulas and finiteness are retained. The unit still reduces through finite schemes, the affine line via its proper projective-line comparison, affine induction with Weil shriek pushforward, and localization. I opened the coefficient-morphism theorem and its current blueprint_update proof to verify that it carries those steps and has no backward dependence on this item. No forbidden SGA route or citation is introduced.

Step 1 uses `sk-d-trace` for the braided-monoidal evaluation/coevaluation definition and its perfect-complex specialization, and `def-trf-categorical-trace` for its ordinary A-valued realization. Both statements actually give the endomorphism ring of the unit as A. This is a trace convention, not a proof of perfectness from notation; Step 5 supplies perfectness by a theorem whose statement says it. No trace on a nonprojective cohomology module is substituted.

Step 2 uses `def-trf-frobenius-coefficient-morphism` for the recursion and its explicit strict-Weil example, `def-trf-iterated-weil-map` for u_m, `lem-trf-iterated-weil-cocycle` for the Weil-map product, and `prop-trf-scheme-galois-comparison` for naturality and multiplicative iterates of kappa. I read each statement. Naturality is applied to phi^[m-1], whose source is the (m-1)-fold Galois pullback of K; the cocycle is used with positive exponents 1 and m-1 only when m>1. The separate base case m=1 avoids using a nonexistent zero-exponent assertion. The resulting composite has the required source L Phi^(m*)K and target K.

Step 3 uses the coefficient-morphism definition's global operator F_c,m(psi)=T_c(psi_m), and `prop-trf-graph-frobenius-operator` explicitly states T_c(u_m)=F_c,K^m for the same strict pair and positive m. These are equal endomorphisms of the same compact-support complex, not merely objects connected by an unspecified isomorphism.

Step 4 uses `thm-trf-frobenius-fixed-points` for the geometric fixed-point equality, `prop-trf-scheme-galois-comparison` for the specified kappa, and the current `def-trf-frobenius-operators` for the exact formulas for rho, tau, and F_y,m. I opened the latter statement: it defines tau by applying the point fiber to the stalk of kappa, composed with rho, so it says exactly what this step takes from it. The pullback equality gives b_y=rho; applying the stalk functor to Step 2 gives the displayed equality with F_y,m by composition. This direct definition-based calculation replaces the older factorization argument, whose intermediate claims were unnecessary. It respects the ordinary coefficient-complex fiber convention of the operator definition.

Step 5 uses `thm-trf-coefficient-morphism-trace-formula`. I matched its field/coefficient data, separated finite-type hypothesis, finite-Tor K, explicit origin witness, chosen compactification and graph/fixed-point admissibility against the item. Its definition of admissibility is the same constructible finite-stage datum; it requires no new strong ambient adjoint hypothesis. Its statement permits noninvertible psi, so the invertible u_1 is allowed. Its actual statement asserts that both sides are traces of perfect complexes in A. Substituting the operator equalities of Steps 3 and 4 therefore yields the first formula without a hidden trace-invariance premise.

Step 6 uses `lem-trf-local-frobenius-conjugacy` clauses (1) and (3), `thm-trf-frobenius-fixed-points`, and `lem-trf-frobenius-degree-formula`. The orbit statement gives exactly d_x lifts and their fixedness when d_x divides m. The degree formula explicitly states the equality of traces with the (m/d_x)-power of one-circuit Frobenius; mere conjugacy is not asked to prove that power formula. The proof writes the elementary finite-domain and residue-field tower arguments showing that a rational point lies above a closed point and its degree divides m. A finite integral domain is a field since multiplication by a nonzero element is an injective permutation; the tower gives m=d_x times the remaining extension degree. Thus points of excluded degree contribute nothing. Each nonempty group has d_x equal summands. This requires repeated addition in A, never division by d_x.

Step 7 uses the fixed-point theorem's explicit finite coproduct description, with one Spec k per rational point. The rational-point index is consequently finite; its nonempty groups give a finite quotient index for the closed-point sum. This finite regrouping is elementary, and the values lie in A by Step 1 and the perfectness assertion in Step 5.

The only generic off-unit theorem inputs left are the comparison and fixed-point theorem, recorded in split_report.tool_uses. They provide Frobenius geometry, not a replacement of the trace-formula unit's route. I read `d-lines` and the coefficient-morphism theorem's affine-line step to check the unit realization: the former defines the line/projective-line charts, infinity complement and Frobenius chart maps; the latter explicitly uses those charts. The current blueprint_update includes d-lines, although the older imported uses list omits it. No other worker's node is changed.

For B1--B10 there are no new-node obligations: no statement-only node was given a proof, no unstated object or duplicated definition was introduced, and no unsupported Mathlib leaf is claimed. For C1--C8 I read every cited statement as described above, retained only premises actually used, checked all 16 verbatim citation certificates and the dependency union, and used the declared generic tools within the fixed unit route. For D1--D5 the proof contains the iterate induction and operator calculations itself; no newly named node hides a clause. For E1--E7 I checked the finite coefficient stage, positive exponents, finite-Tor/origin/admissibility hypotheses and exact objects at each application, including canonical stalk identifications. There is no unproved transport assertion left in Step 4.

Small cases checked: m=1, empty X_0, K=0, shifted perfect complexes, and X_0=Spec F_(q^d). In the last case no points occur when d does not divide m, and otherwise there are d lifts with equal trace, giving the required multiplier. The case ell dividing d confirms that d need not be invertible in A. Nonreduced X_0 is allowed by the statements used. A two-term perfect complex [A --ell--> A] over Z/ell^2 has identity supertrace zero; this checks why finite cohomology modules alone cannot replace perfect-complex traces. No new statements need further edge-case testing.

## Validation and unfinished work

Citation certificates cover exactly the 16 step/node pairs and are exact substrings of current cited statements. The item's proof_deps is the union of its step uses. Only the permitted unit-realization fields changed in the unit file. The required server review and full deliver.py --no-push are run after this repair; a READY handoff is made only on an OK dry run. No delivery is pushed. The one-level split is complete; open premises remain existing DAG work for later workers. A fresh second reader must review this version and deliver it.

## Second reading by Q67

Independent second reader, 2026-10-17. I opened delivery-errors B–E, GOAL, dag-sync, the current main-20261015 item statement/proof and chapter/unit records, and every cited node statement. The item has no Stacks-tag source and introduces no new nodes: its direct source is the blueprint, and its coefficient-morphism premise carries the prescribed finite-scheme, projective-line/affine-line, affine-induction and localization route. I also read the corresponding blueprint sources for the iterates, cocycle, graph operator, comparison, local operators, conjugacy and degree formula. No forbidden SGA source is used.

- Item statement: checked against main-20261015 thm-trf-grothendieck-lefschetz-finite-ring.md, every hypothesis and both formulas; PASS. Separated finite type, finite-stage strict pair, finite Tor amplitude, explicit origin witness and specified admissibility/compactification datum are retained. The statement differs from the base only in whitespace.
- Step 1: checked sk-d-trace and def-trf-categorical-trace against the perfect-complex convention; PASS. Reading the evaluation composite as an element of A is elementary once perfectness is supplied in Step 5.
- Step 2: checked the recursion/example in def-trf-frobenius-coefficient-morphism, u_m in def-trf-iterated-weil-map, natural multiplicative kappa in prop-trf-scheme-galois-comparison, and the positive-exponent cocycle statement; PASS. Naturality is used at the object Lg_gamma^((m-1)*)K, and the cocycle uses (1,m-1) only for m>1. The coefficient ring is finite and annihilated by an ell-power invertible in k, as comparison requires.
- Step 3: checked the global-operator definition and the strict-pair clause of prop-trf-graph-frobenius-operator; PASS. They give equality of endomorphisms of the same compact-support complex, not just conjugacy of unspecified objects.
- Step 4: checked the canonical fixed-point map in thm-trf-frobenius-fixed-points, the current precise rho/tau formulas in def-trf-frobenius-operators, and the specified comparison; PASS after making the ordinary point-fiber functor explicit. Applying that functor to Step 2 and preserving composition is the displayed calculation, with no additional geometric transport theorem assumed.
- Step 5: checked every hypothesis and the perfectness conclusion of thm-trf-coefficient-morphism-trace-formula; PASS. Its noninvertible coefficient-map domain includes u_1. The finite-stage admissibility definition specifies the constructible adjunction, not a stronger ambient adjoint. Substitution uses Steps 3 and 4 only.
- Step 6: checked clauses (1) and (3) of lem-trf-local-frobenius-conjugacy, the fixed-point bijection, and the statement (not its proof) of lem-trf-frobenius-degree-formula; PASS. The affine image is a finite domain, hence a field by injective multiplication on a finite set; the residue-field tower gives d_x dividing m. Applying the fixed-point bijection with m=d_x supplies the chosen one-circuit lift. There are d_x equal summands, and multiplication by d_x is repeated addition, requiring no invertibility.
- Step 7: checked the finite coproduct assertion of thm-trf-frobenius-fixed-points and the finite partition of Step 6; PASS after explicitly referring to Step 5 for perfectness. Finiteness of the quotient index and finite regrouping are elementary.
- New nodes: none; zero new nodes and zero Mathlib leaves. No elementary fact, duplicated lemma, or item clause was turned into a new obligation; B1–B7 have no new-node instance to repair.
- Unit realization: checked the four recorded unit steps against the coefficient-morphism theorem's current proof and d-lines; PASS. Only realized and realized_by differ from the shared unit record. The comparison and fixed-point nodes are proposed generic tools in split_report, for maintainer acceptance, not an installed unit-route exemption.

Small cases independently checked: m=1 uses the induction base only; empty X_0 and K=0 give zero and empty sums; n=1 gives field coefficients, and n>1 still requires perfect-complex traces; for Spec F_(q^d), the sum is empty if d does not divide m and otherwise consists of d equal traces. When ell divides d the multiplier may vanish in A, which is correct and shows why division cannot be used. A shift changes both traces by the same sign. The datum excludes n=0 and m=0; no such case has been silently added or discarded.

Changes made by the second reader:

- Expanded Step 4's shorthand stalk calculation into the explicit functor S_y=Fib_s composed with L ybar^*, using M=For(K,varphi), so all displayed arrows are ordinary coefficient complexes with identified domains.
- Added the Step 5 perfectness reference in Step 7, so A-valuedness cites its hypothesis as well as the trace convention.
- Expanded the Step 2 comparison and Step 6 degree-formula citation excerpts to their full verbatim statements, exposing their hypotheses; the same 16 citation pairs remain.
- Added this independent second reading; the first worker's sections, including Review by Q67, are preserved.

Validation: the initial server dry run passed at 350df7a394. All 16 certificate pairs were checked against the opened current statements and are exact verbatim substrings. The repaired version is dry-run again before delivery; its outcome is recorded below.

Repaired server dry run: OK (not pushed) at b3874ea4db, preflight passed, including the server DAG and split-review checks. Delivery follows with the same node and citation content.
