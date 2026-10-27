# Q159: lem-pur-scalar-composite-mate-adjunct

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-scalar-composite-mate-adjunct.json — statement, now split; no exact Mathlib match. Four proof steps use only existing nodes.
- citations.json — verbatim statement quotations for all three step/node citations.
- searches.jsonl — actual Q159 msearch output summaries, retained without alteration.
- report.md — this report. write_split.py is a sandbox-only JSON preparation script, not a delivery node.

New nodes: 0. New Mathlib leaves: 0. No unit record changes: this item is not the unit's key node. Repository and Lean sources were read only; no git command, Lean edit, compiler or Lake invocation was run.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, scalarMate, scalarPullbackIso, scalar/composition terminology and the related etale pullback module. There is no project declaration stating this whole transported-adjunct equation. ExtendScalarsComp.lean supplies an underived scalar comparison for abelian sheaves, not this arbitrary-ring unbounded mate assertion. The existing DAG node lem-sf-scalar-pullback-composition has the exact normalized scalar comparison clause needed by Step 3, with its existing Sheaf.Paper.ScalarPullbackComposition interface and reviewed proof. It is cited, not claimed as an attachment for the item.

## WANTED

None: the source of the construction and the cited comparisons is available locally.

## Audit findings and changes

The live item was unsplit with empty proof. No prior sandbox node/report/search log was present. Its statement is correctly typed and unchanged. Its original Q149 searches, provenance, chapter/unit and blueprint ancestry were retained, and the actual Q159 searches were appended. The ancestry is cor-pur-vector-bundle-purity through lem-pur-etale-direct-image-scalar-composition and lem-pur-etale-compact-scalar-coherence. The blueprint search found no blueprint node stating this particular equation.

The source's Tag 0E46, remark-compose-base-change, explicitly omits the verification. The split supplies the missing calculation instead of treating that remark as a proved one-step argument. In particular, the statement of lem-weil-pbc-ringed-topoi-derived-pushforward-composition alone gives the normalized isomorphism but does not explicitly give counit compatibility. Step 1 therefore uses lem-sfb-ringed-derived-monoidal-comparisons, whose statement does give that exact compatibility. The second required input already exists as lem-sf-scalar-pullback-composition; no duplicate scalar-pullback lemma was created.

The proof follows the coefficient-reduction/adjunction-composition subargument of paragraph 2 of the current vector-bundle proof. Generic comparison results are used as tools; no purity theorem is assumed. Both off-unit tools are declared with reasons in split_report.tool_uses.

## Unfinished work

None in the authorized stage-1 split. This is a natural-language proof delivery, not a claim of a new Lean proof.

## Not duplicates

No new nodes. Reused lem-sf-scalar-pullback-composition for the scalar square and lem-sfb-ringed-derived-monoidal-comparisons for the specified compositor's counit equation. The item proves an intermediate transported adjunct equation, whereas its existing parent lem-pur-etale-direct-image-scalar-composition compares two direct-image scalar mates and also proves the identity clause. The parent is not cited, avoiding a circular proof.

## Review by Q159

I read the chapter and sk-prop-an unit, the live item and its parent's proof, and the current main-20261015 cor-pur-vector-bundle-purity.proof.md, especially paragraph 2 on coefficient reduction and composition before transposing. In literature/stacks-project/sites-cohomology.tex I read lemma-adjoint (07A6), lemma-derived-pushforward-composition (0D6E), remark-base-change (07A7), and remark-compose-base-change (0E46). The tags were checked against tags/tags. The source explains the counit-defined mate and identifies pushforward composition by adjunction; the last verification is omitted there, so proof_origin is honestly agent, with the local source and exact place recorded.

Step 1 uses the statement of lem-sfb-ringed-derived-monoidal-comparisons, which I opened in full. It explicitly specifies the K-injective kappa, K-flat c, and compatibility with the composite adjunction and its counit, without flatness or boundedness. Specialize separately to the constant rings A and B. The hypotheses hold because scheme maps induce ringed-topos maps on the chosen small etale sites and the constant-ring module inverse images are the exact geometric inverse images already specified in the item's statement. Expanding the phrase 'under those comparisons' gives epsilon_sr = E followed backwards through P_r P_s(kappa) and c in the exact order displayed in Step 1. Here and throughout formulas use the standard right-to-left composition convention.

Step 2 uses only the statement of def-pur-etale-scalar-mate, opened in full: its component is by definition the geometric-adjunction transpose of scalar extension of the counit preceded by lambda. Thus epsilon_B composed with P_B(chi) is exactly that map, not an additional base-change theorem. I checked the naturality arrows explicitly. With W=R_sr,A(M), k:W→V, the first expanded formula has domain P_r,B P_s,B Q_Z(V); the rightmost arrow takes it to P_r,B P_s,B Q_Z(W), then c_B inverse to P_sr,B Q_Z(W). Naturality moves Q_Z(k inverse) through c_B inverse and lambda_sr and gives Q_X(epsilon_sr,A composed with P_sr,A(k inverse)). All these are categorical naturality and functoriality substitutions; this is why this step is elementary after the cited definition and Step 1.

Step 3 uses the statement of lem-sf-scalar-pullback-composition, opened in full including its recorded Lean interface. It concerns arbitrary ring maps and scheme maps, all unbounded small-etale complexes, and precisely scalarPullbackIso transported along Lf*=D(f*). Taking j1=r, v=s, j2=sr and its evident equality gives the displayed square. Its composition comparisons are the canonical module inverse-image ones, adjunction-normalized; the ringed comparison of Step 1 is computed by ordinary pullback composition on K-flat representatives, so these are the same specified comparisons. I also read lem-weil-pbc-inverse-image-composition-module-linear and prop-weil-pbc-inverse-image-modules-exact to check that convention and the equality of exact inverse image with module pullback. No comparison is identified merely because an isomorphism exists. Cancelling c_A and c_B in that square is a two-line manipulation and supplies precisely the next expression for Adj_B(F).

Step 4 uses prior proved formulas only. Naturality of c_A at k inverse moves it through the inverse compositor; Step 1 leaves P_r,A P_s,A(k) next to P_r,A P_s,A(k inverse), which cancel. Applying Q_X and its composition law produces T_M in the exact order in the statement. This is elementary and uses no new lemma. Every node cited in a step is covered by a verbatim quotation in citations.json. I checked each quote against that node's statement, not its proof. The parent is never used, and a dependency traversal of the tools found no path back to this item.

For Mathlib I ran both natural-language phrasings with leanfinder, LeanSearch, two Loogle queries and two source greps via msearch. All returned successfully. I read Adjunction.comp_counit_app at Mathlib/CategoryTheory/Adjunction/Basic.lean:580, mateEquiv_hcomp at Mates.lean:209, and conjugateEquiv_counit and conjugateEquiv_counit_symm at Mates.lean:285 and :291. These supply generic categorical calculations; they do not identify the specified derived normalization, so the whole item is not a one-line specialization. The remaining hits concern underived module adjunctions, pullbacks of sheaves, or exponentiable morphisms. No new leaf or generic mate lemma is necessary for the explicit elementary calculations here. Only searches actually run are recorded; inherited Q149 records are preserved as inherited records, not represented as searches by Q159.

I checked the B–E return criteria against this delivery. B: no new non-self-contained or proof-containing node, no fabricated searches, and exact blueprint provenance retained. C: every non-elementary comparison is a cited statement; the two generic off-unit tools are declared, and there is no cycle. D: the proof carries the transport, naturality and cancellations itself; it does not repackage its conclusion in a new node or use the parent's conclusion. E: morphism domains, inverse orientations, coefficient rings and lack of bounds/flatness are checked at each substitution. All proof steps are under 2000 characters and hide no extra comparison lemma. I tested identity r or s, identity A→A, the empty scheme, the zero complex, and the nonflat coefficient map Z/4→Z/2: every cancellation is of an explicitly invertible compositor, and the proof never inverts chi or assumes ordinary scalar extension exact. Hence the small and nonflat cases introduce no missing hypothesis. No statement dispute or route departure was found.
