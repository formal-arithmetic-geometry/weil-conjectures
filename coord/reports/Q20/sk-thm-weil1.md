# sk-thm-weil1 — Q20 stage-1 split

## Files written

- `dag/nodes/sec-zeta-weil/sk-thm-weil1.json`: item, statement, split into two applications of existing statements; no Mathlib match.
- `dag/units/sk-thm-weil1.json`: only `realized` and `realized_by` filled, with the item carrying the statement and the sole assembly step.
- `citations.json`: verbatim statement quotations for both proof citations.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None claimed for the item. `AlgebraicGeometry.Scheme.zetaSeries_rational`, `WeilConjectures/Statement.lean:80`, has an explicit `sorry` in this read-only source, so it cannot close this item. `AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`, `WeilConjectures/EulerProduct.lean:49`, has a proof and already belongs to `prop-euler-product`, but states only the Euler-product clause. `ZetaIntegrality.lean` contains the coefficient-integrality declarations, which still do not supply rationality. Searches for the exact blueprint id/tag found no declaration of the whole item. No upstream-master sorry declaration was treated as a proof.

## WANTED

None. The item's assembly proof and both cited statements are present in the current blueprint. This split follows that blueprint, an agent-written source, and accordingly has `proof_origin.by = agent`; it does not claim to follow a Stacks theorem or an unread human-authored paper.

## Corrections and source observations

The item statement agrees verbatim with `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-thm-weil1/_section.md` and was preserved. Its imported proof said “closed-point product and integrality” but omitted the relevant node from `uses` and `proof_deps`. The proof now cites `prop-euler-product`, the existing node of the `sk-prop-euler` unit (there is a unit and current blueprint sketch with that id, but no separate DAG node `sk-prop-euler`). This is precisely the route of the unit's sole step, not a substitute proof route.

The current blueprint's `thm-weil-final-rationality.md` states the same arbitrary-finite-type theorem, including the normalized integral polynomial presentation; this is recorded in `blueprint.same_as`. The older reviewed DAG statement of that node still has smooth, proper and geometrically connected hypotheses. Its `blueprint_update` records the new statement. It is not used in this proof, so no stronger geometric hypotheses are silently imported.

The statement dependencies now also name the existing polynomial-ring, formal-power-series, and rational-power-series definitions. In particular, “membership in Q(T)” has its Taylor-series meaning, not a claim that a formal series is literally a rational-function term without an interpretation.

## Unfinished work

None in this one-level split. The rationality statement is an existing imported theorem node and remains its own task. Its statement already contains the stronger integral normalized presentation, so this item does not attempt to get B(0)=1 by merely clearing rational denominators. No new lemma hiding this issue was introduced.

## Not duplicates

No new nodes. The whole DAG and blueprint were searched by Euler-product and rationality terminology (`blueprint_refs.py search` and `rg`), and the existing statements were reused. The two apparent duplicates at the sketch/detailed-blueprint levels are handled by citing the existing Euler-product node and recording the current final-rationality theorem in `same_as`.

## Review by Q20

I read the chapter, the `sk-thm-weil1` unit, the current main-20261015 item statement and its separate proof file, and both the sketch and detailed Euler-product source statements. I also read the current `sk-thm-rationality` source statement and the actual DAG statements of both cited nodes. The item is an assembly theorem: its proof really can stop at these two existing results.

For Step 1, `sk-thm-rationality` says, for an arbitrary scheme quasi-compact and locally of finite type over Fq, that there are A,B in Z[T], B(0)=1, and BZ=A in Q[[T]], and explicitly gives membership in Q(T) intersect (1+TZ[[T]]). These are exactly the first clauses this step uses. The finite-type hypothesis is identical on the item and the cited theorem. I verified that no properness, smoothness, connectedness, separatedness, or coefficient-realization hypothesis has been added. Reversing the two sets in an intersection is an elementary logical rearrangement, written in the step. There is no non-elementary rationality descent or Fatou argument hidden in this assembly step: those belong below the already existing theorem whose full statement is cited.

For Step 2, `prop-euler-product` explicitly asserts both Z equal to the product over closed points and its integral coefficients. It also explicitly states coefficientwise local finiteness, which is what this step takes to interpret the product in Q[[T]]. Applying it with Y0=X0 uses exactly finite type over Fq. The degrees are the residue-field degrees from the item's zeta definition. I checked that the current blueprint Euler proposition and its detailed node use this same point-count series. No analytic convergence theorem or finite-field Euler product for number fields is being substituted for this formal identity. Both proof uses have verbatim complete-statement quotations in `citations.json`.

I checked B–E of `coord/delivery-errors.md`: there are no new incomplete or redundant statement nodes, no unlogged Mathlib queries, no tag-only citations, no use of a cited proof's private construction, and no added hypothesis. Each of the two non-elementary inputs is a cited node with the needed conclusion; there are no fresh nodes restating an item clause. The Mathlib searches were run through `msearch.py` in all four modes, and repeated with a second phrasing before recording no match. Their actual results are recorded: analytic Riemann/Dedekind zeta products, partition products, and general Laurent/power-series facts do not state this scheme theorem. The Loogle unknown-identifier result is retained as reported, not described as a service outage.

As small cases, the empty scheme has Z=1 and the empty product is 1, allowing A=B=1. A rational point gives Z=(1-T)^(-1), with A=1 and B=1-T. A single closed point of degree r gives Z=(1-T^r)^(-1); finite disjoint unions multiply these factors. These check the constant coefficient, the sign of the Euler-factor exponent and the lack of a geometric-connectedness hypothesis. Neither citation imposes reducedness, so nilpotents introduce no extra hypothesis here. The item itself is true as stated, so no STATEMENT-DISPUTED correction was needed.

## Second reading by Q20

- Item statement: checked hypothesis by hypothesis against main-20261015 `sk-thm-weil1/_section.md` and the unit's assembly paragraph; PASS, including arbitrary finite type, integral A,B, B(0)=1 and equality in Q[[T]]. The chapter's smooth-proper overview does not override this explicitly stated finite-type theorem. No statement dispute.
- Step 1: opened the actual statement of `sk-thm-rationality` and its main-20261015 `_section.md`; PASS, it supplies the integral normalized presentation itself, not just rationality over Q, under exactly quasi-compact plus locally finite type. The only elementary rearrangement is exchanging the order of the intersection's two membership conditions. No use of its proof or hidden Fatou lemma.
- Step 2: opened `prop-euler-product`, main-20261015 `sk-prop-euler/_section.md` and `prop-euler-product.md`, and both `sk-def-zeta` and `def-weil-point-counts-zeta`; PASS after explicitly identifying the two exponential point-count formulas and the residue-field degrees. The cited product is coefficientwise locally finite and uses only finite type. All four citations across the two steps now have complete verbatim statement quotes in citations.json; the elementary definition comparison needs no new lemma.
- New nodes: none; B1–B7, new-node duplicate/specialization/restatement checks and new-leaf declaration/line checks are vacuous. Existing Euler and rationality results were reused. Independent `msearch.py` queries used the exponential point-count formulation (LeanFinder), `AlgebraicGeometry.Scheme, RatFunc` (Loogle) and `rational.*zeta|zeta.*rational|closed.point.*product|pointCount` (grep); no match. Actual returned hits are partition/exponential power-series results and Configuration.pointCount, unrelated to scheme rationality. All searches are in searches.jsonl and the item's search records.
- Small cases: empty scheme gives Z=1, A=B=1 and empty product 1; Spec Fq gives Z=(1-T)^(-1); Spec F_(q^r) gives Z=(1-T^r)^(-1) since its point count is r when r divides n and 0 otherwise. At degree 0 every product is 1; modulo T^2 only degree-one points contribute. Finite disjoint unions and nonreduced zero-dimensional schemes introduce no missing connectedness or reducedness hypothesis.
- Lean attachment check: read Statement.lean:80–84 (explicit sorry), EulerProduct.lean:49–74 (proved Euler product only), ZetaIntegrality.lean:66–110 (integrality and constant coefficient), and Rationality.lean:104–110 (requires a trace datum). No complete sorry-free declaration closes the item. The existing Euler node's closed audit omits its integrality clause, as its blueprint_notes already warns; this split uses its natural statement, not that inaccurate completeness claim, and does not alter the maintainer-owned audit.
- Unit and route: checked dag/units/sk-thm-weil1.json; only realized/realized_by change. Both proof inputs are in its specified route, and the two item steps realize its sole assembly paragraph. The older smooth-proper `thm-weil-final-rationality` DAG statement is not an input; same_as refers explicitly to its broadened current blueprint_update.

Changes made: added `def-weil-finite-type-morphism` and `def-weil-point-counts-zeta` as existing statement dependencies; wrote the elementary identification of sketch/detailed zeta formulas and degrees in Step 2 with both definition citations; updated proof_deps and verbatim citations accordingly; recorded three independent Mathlib searches. The statement, rationality application, Euler-product application and first worker's review are preserved. No new nodes or Mathlib leaves.

Dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q20 sk-thm-weil1 --no-push .` printed `OK (not pushed) deliver/Q20/sk-thm-weil1 at 827579a160: preflight passed`. The required maintainer preflight ran on the Weil server; no check_dag.py, review_split.py or preflight_delivery.py was run locally.
