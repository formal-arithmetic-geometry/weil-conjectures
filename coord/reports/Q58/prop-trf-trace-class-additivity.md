# Stage-1 worker report: prop-trf-trace-class-additivity

## Files written

- `dag/nodes/sec-trace-formula/prop-trf-trace-class-additivity.json`: five proof steps, reusing existing nodes; Mathlib searches found no match.
- `dag/units/sk-i-additivity.json`: only `realized` and `realized_by` are changed, binding the existing unit record to this item.
- `citations.json`: verbatim statement excerpts for every dependency of every step.

No new nodes; no Mathlib leaves. The sandbox's root `repair.py` is only an editing aid, not a delivery file.

## Attachments

None. I searched `WeilConjectures/` by the item id and by trace/additivity names and read `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Localization.lean:247–273`. `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass_graph_eq_traceClass_add_traceClass`, at line 258, ends in `sorry` at line 273. Its Lean statement covers graph trace additivity for stable closed/open pieces, with compactification and finite-Tor hypotheses; it does not itself state both clauses and componentwise local terms of this item. It cannot be attached. No Lean was written or compiled.

## WANTED

None. This proof follows the local blueprint and already stated DAG interfaces, with `proof_origin.by = agent`; it does not claim to have reconstructed the filtered trace theorem from external literature.

## Corrections and discrepancies

STATEMENT-DISPUTED: the imported statement starts with a closed immersion on an unintroduced $X$ and then uses unintroduced $c,K,A,F$. Its curve clause points to “the setting” of another node instead of introducing the objects. I made the implicit coefficient and admissible-correspondence context explicit, including the finite-Tor domain required by `def-trf-trace-class`, and expanded the curve data from `d-curve-pieces`. This repairs missing bindings and implicit hypotheses faithfully to the source interfaces; the invariant-decomposition and curve conclusions are unchanged. The original unused scheme-properties dependency is replaced by the definitions that actually supply these notions.

The previous seven-step attempt repeated a connecting-square proof using a Hom-vanishing statement for the wrong source object. Its adjunction dependency was stated only for finite constant coefficients in ambient categories, whereas its text also invoked a generic exact-derived-functor lemma without supplying exactness of the relevant abelian functor. I removed this duplicate argument: the existing `lem-trf-trace-triangle-compatibility` already states ALL three compatibilities for the induced maps and explicitly identifies its Frobenius specialization with `d-curve-pieces`. The present proof checks those induced maps and invariance before using that statement. No new node restates a clause of this item.

The current `main-20261015/sk-i-additivity/_section.md` has a broader stable closed/open graph statement (including $m=0$) than the still older `dag/units/sk-i-additivity.json` curve-sketch text. I did not edit either unit statement or its maintainer metadata. The item continues to state precisely the two clauses in its current node source. Its general clause applies to invariant graph decompositions as well; its curve local-term clause retains $m\geq1$, which is essential for the finite-fixed-point input.

The earlier report's claim that the Lean theorem was “exactly” this item's curve conclusion was too strong: its statement has no local-term clause. Also, the permission to declare generic cross-unit tools in `split_report.tool_uses` is explicitly given in the later SETUP and brief rule; no maintainer-owned top-level `tool_uses` was written.

## Unfinished work

None for this one-level split. The filtered localization trace theorem remains the existing cited node's task. This delivery introduces no new theorem or definition.

## Review by Q58

I read the current main-20261015 item statement and proof, the chapter and DAG unit records, the current unit `_section.md`, `d-curve-pieces.md`, `lem-trf-trace-triangle-compatibility.md`, `def-trf-local-term.md` under `sk-d-pairing`, and `lem-trf-integration-linear.md` under `sk-d-integral`. I read the fixed-point theorem's DAG statement, its recorded master source under `sec-six-functors/sk-prop-sf-rf-shriek-preservation`, and its current main source under `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation`. I also opened the DAG statements defining coefficient conventions, correspondences, trace classes, fixed schemes, integration, and Frobenius coefficient morphisms. These confirm separated finite type, $A=A_{E,n}$, $K\in D^b_{ctf}$, admissibility, and the restriction of scalar integration to proper components. There are no new-node sources to audit.

Step 1 uses `lem-trf-trace-triangle-compatibility`: its statement gives both the exact induced maps and the trace equality for the exact set-theoretic invariance hypothesis in the item. Step 2 uses `def-trf-local-term`, whose statement says the clopen components are proper when the ambient fixed scheme is proper and gives their integral formula, and `lem-trf-integration-linear`, whose statement gives the required equality with scalar $1$. Preservation of addition under the restriction functor and composition with the fixed identifications is the elementary part of this step; no further duality or base-change theorem is invoked there.

Step 3 uses `d-curve-pieces`, which actually asserts $\Phi_m i=i$, the Cartesian open square, the point pushforward formula, the open extension formula, and applicability to arbitrary coefficient morphisms. Computing $c_2(c_1^{-1}(Z))=Z$ is immediate because the first graph leg is the identity. `lem-trf-trace-triangle-compatibility` explicitly says that its induced maps in the Frobenius case ARE these pieces, so this is an assertion in its statement, not an extraction from its proof. Step 4 uses that same lemma for the induced triple and its trace identity; commutativity of addition changes the displayed order of the two terms. In particular, the connecting square is supplied by the cited lemma itself, and no unsupported morphism-completion or factorization fact remains.

Step 5 uses `thm-trf-frobenius-fixed-points` for the finite coproduct of reduced $\operatorname{Spec}k$ components, and the point-component clause of `def-trf-local-term` for their properness and integrals. `lem-trf-integration-linear` then applies with exactly its properness and admissibility hypotheses. This avoids an uncited general finite-implies-proper theorem: each point component's properness is explicitly supplied by the local-term node. `d-curve-pieces` supplies the last arbitrary-$v$ observation. The fixed-point theorem is the only declared cross-unit generic tool; it supplies no alternative trace-additivity route.

I checked B–E against the final files: all objects and notions are introduced and have definition dependencies; every used non-elementary fact is stated by a cited existing node; quotes were copied from those statements; the new-node, duplicate-tag, and new-node Mathlib-leaf cases are vacuous. DAG and whole-blueprint searches for “trace class” and “additivity” found the existing induced-localization lemma and the distinct global compact-cohomology trace proposition. The latter is about scalar categorical traces, not this equality of Verdier classes on the fixed scheme, so it is not a duplicate. The item has no other equivalent blueprint node (`same_as = []`).

The five Mathlib searches were run through `msearch.py` and recorded with their actual queries: two semantic phrasings, quoted-name Loogle, Mathlib/CategoryTheory grep, and LeanSearch. The results concern additive functors, matrix/direct-sum traces, ordinary triangle completion, or Lean debugging trace classes, not the Verdier correspondence trace map. No match or unavailable service was fabricated.

Small-case checks: in the generic clause $Z=\varnothing$ or $U=\varnothing$ makes one piece zero and gives the expected identity; $u=0$ is allowed. In the curve clause $v=0$ and noninvertible $v$ use the same induced-map formulas. A single fixed point has precisely the point integral. An empty fixed scheme makes the componentwise assertion vacuous. I checked the boundary $m=0$: the generic clause still applies to the identity graph, but the finite-fixed-point conclusion may fail, so the curve clause and its use of the theorem retain $m\geq1$. No new statement excludes these legitimate edge cases, and no argument assumes invertibility. No SGA 4 or SGA 4½ source, Lean write, build, or compiler is used.

## Earlier second reading (a previous round; superseded)

- Item statement: compared both clauses with main-20261015 `sk-i-additivity/prop-trf-trace-class-additivity.md` and its proof; the explicit separated finite-type, finite-Tor, admissible-correspondence context is exactly the context of `def-trf-correspondence` and `def-trf-trace-class`, not a new restriction. The curve data match `d-curve-pieces`; $m\geq1$ and arbitrary noninvertible coefficients are retained. PASS.
- Step 1: read the full statement of `lem-trf-trace-triangle-compatibility`, including its current blueprint update; it states the invariance condition, precisely these induced maps, all triangle squares, and the claimed trace identity. The item does not claim arbitrary triangle-map additivity. PASS.
- Step 2: read `def-trf-local-term` (including its exceptional-admissibility convention and restricted-section formula) and `lem-trf-integration-linear`; proper clopen components have the needed integral, restriction is additive by the displayed pullback/composition formula, and linearity at scalar $1$ gives the result. PASS.
- Step 3: read `d-curve-pieces` and the Frobenius-identification clause of `lem-trf-trace-triangle-compatibility`; $c_1=\operatorname{id}$ and $\Phi_m i=i$ prove invariance, and both map formulas, including the arbitrary-$v$ case, are in the cited statements. PASS.
- Step 4: compared with the same lemma and source proof paragraphs (a)–(c); the lemma explicitly includes the connecting square, so the step uses its statement rather than the flawed triangle-completion argument hidden in its imported proof. Addition in the stated Hom group permits reversing the two summands. PASS.
- Step 5: read `thm-trf-frobenius-fixed-points`, its current source, the point-component clause of `def-trf-local-term`, the full integration-linearity statement, and the arbitrary-map paragraph of `d-curve-pieces`; $m\geq1$ gives finitely many reduced clopen points, each proper, and scalar-$1$ linearity gives componentwise local terms. Expanded the restriction and integration equations. PASS.
- New nodes: none; B1–B7, duplicate-node searches, new-node Mathlib searches, and new-node small-case checks are vacuous. No Mathlib leaf is claimed.
- Citations: checked every `(step,node)` against its uses list and every quote as an exact substring of the cited current statement; all ten citations match. PASS.
- Edge cases: $Z=\varnothing$, $U=\varnothing$, zero coefficient morphism, empty fixed scheme, one reduced fixed point, and $n=1$ preserve the formulas. $n=0$ is outside the coefficient convention; $m=0$ is allowed by the generic graph clause but deliberately absent from the finite-fixed-point curve clause. No inverse of $v$ occurs. PASS.

Changes: replaced Step 5's “exactly as in Step 2” with the explicit restricted trace equality and its integrated equality (E5). Kept the sound statement, other proof steps, existing dependency nodes, first worker's review, and verbatim citation quotes. No Lean or live-project file was written, no compiler/build was run, and no SGA source was added.

## Repair of landing return (2026-10-17, returned head b0e6e08377)

The return identified one changed dependency: `def-trf-local-term`. I compared the retained delivery with the current shared DAG without running git in the shared repository. I reconstructed the item from the current node plus this item's retained split fields, and reconstructed the unit from its current record plus only `realized` and `realized_by`. The normal delivery tool will base its temporary delivery commit on current server main; no push is authorized for this worker.

I reread the full current local-term definition and compared it to both stale quotations. Its changes distinguish the coefficient field from the ambient scheme, spell out the constant-coefficient pullback identification, cite properness of clopen components, and require the singleton point to be BOTH open and closed before using its reduced open subscheme. It now explains the integral zero-dimensional point argument and explicitly restricts Frobenius to positive exponent and the k-linear base change of scheme Frobenius. These changes preserve the local-term formula needed here. Steps 2 and 5 are materially updated, and both quotations are recopied from the current statement, rather than merely rebasing the returned content.

For Step 2 I checked the current restricted-section composite and its two fixed identifications: applying the additive derived pullback and composing with these identifications preserves sums. The same definition explicitly states properness of each clopen component of proper F. No reduction is applied to those components. Its exceptional-admissibility convention remains in force, exactly as required by the unchanged integration-linearity statement. For Step 5 the fixed-point theorem supplies a finite coproduct of reduced Spec k points. Each singleton is both open and closed and its actual open subscheme is reduced, so the revised point-component clause applies directly. The exponent is m >= 1 and Frobenius is the base-changed scheme Frobenius, as required by both current statements. Zero and noninvertible coefficient maps still use exactly the same formulas. The empty fixed scheme remains vacuous.

I also reread every other statement dependency (coefficient conventions, correspondence, fixed scheme, trace class, curve pieces, induced triangle compatibility) and every other proof dependency (integration linearity and Frobenius fixed points). All eight retained quotations from those proof dependencies still occur verbatim. Step 1 still uses the invariant-decomposition lemma with its precise invariance condition; Steps 3 and 4 still use its explicit identification with curve pieces and its complete induced triangle compatibility, including the connecting square. None of these uses changes a coefficient category, assumes invertibility, or replaces the unit's trace route. The original main-20261015 item and proof, its local-term definition, and its current unit source were reread; the current DAG local-term statement is more explicit than that imported source and is the interface used for this repair. The slopmaster2 trace-additivity theorem was rechecked at Localization.lean:258–273 and still ends in sorry, so there is no attachment. The retained search log was read, including the five queries used by the split; their search questions have not changed and they were not rerun. No new node, Mathlib leaf, source citation, Lean file, build or compiler call was introduced.

The earlier Review and Second reading sections above are retained history of the returned split; this repair revalidates their local-term claims against the changed statement and awaits a fresh second reader. B1–B9 and duplicate-new-node checks have no new-node cases; C1/C3/C4 are checked against each current proof-dependency statement, and D1/D2 are avoided by using the pre-existing triangle lemma rather than creating a restatement. The scheme and coefficient hypotheses and the small cases just described check E1–E6.

Current cited-statement SHA-256 fingerprints at this repair reading (for the next reader to detect later changes):

- `d-curve-pieces`: `4186fd93397d862653fc277877c011d2404cf1b89bf5dcdf23d52cc106b52cc2`
- `def-trf-coefficient-conventions`: `c84f93c1d04d26cc56757ed8a2a45ce00be992457729690861052b4ae1b7a4f3`
- `def-trf-correspondence`: `6fb211fc2a6e4d0801e8e9f577c9d96878fa1c81ee70d61cb7035a1c3bb7315a`
- `def-trf-fixed-scheme`: `0b204d0c9b938268016caa577dc1e2cf62938b5bd3d1d14034511aaa378f22ae`
- `def-trf-local-term`: `8cbbe85abe30493724570ceb87d91d87159328b38196ef04c1e4bc67e2334530`
- `def-trf-trace-class`: `4b53ef7a37610024ae63af1343335743722c968b15e8f9b8aed86c3eaec37faa`
- `lem-trf-integration-linear`: `fcf737a288667a0d342c84d0686c92eb7ae8eda01c10a0bd8c2b19011aec8508`
- `lem-trf-trace-triangle-compatibility`: `e7e66ec23db2936dec50bc123670a7c883baa18e736dba9a905eb9a1f1957c6a`
- `thm-trf-frobenius-fixed-points`: `fd43feadab0d6b41f70ac1ecbdff329625d23f27d56a64a35a08d38a299e6d7c`

## Second reading by Q58

- Item statement: checked both clauses against `main-20261015` `prop-trf-trace-class-additivity.md`, the current unit section, and all statement dependencies; the finite-field, coefficient, separated finite-type, finite-Tor, admissibility, invariance, proper-component, curve, and m≥1 hypotheses are present, and the two conclusions retain their exact order and Hom/local-term targets. PASS.
- Step 1: checked against the complete statement of `lem-trf-trace-triangle-compatibility`; its stated invariance condition, induced maps, triangle morphism, and trace-class equality supply exactly the step. PASS.
- Step 2: checked against the current `def-trf-local-term` and `lem-trf-integration-linear`; component restriction is additive by the displayed pullback/composition formula, and properness plus exceptional admissibility are the stated integration hypotheses. PASS.
- Step 3: checked against `d-curve-pieces` and the Frobenius-specialization clause of `lem-trf-trace-triangle-compatibility`; Φ-invariance, Cartesian open restriction, point pushforward, open extension, and arbitrary coefficient-morphism applicability are all stated. PASS.
- Step 4: checked against the same triangle-compatibility statement; all three induced compatibilities, including the connecting square, and the trace identity are stated, while reversal of the two summands uses commutativity in the displayed Hom group. PASS.
- Step 5: checked against `thm-trf-frobenius-fixed-points`, the point-component and endocorrespondence clauses of `def-trf-local-term`, `lem-trf-integration-linear`, and `d-curve-pieces`; finite reduced Spec k components are open and closed, proper, and support the asserted componentwise integrals for m≥1, with arbitrary v. PASS.
- Citations: verified all ten `(step,node)` quotations against the current DAG statements; each is an exact substring and each cited statement says what its step uses. PASS.
- New nodes: none; B1–B7 (including self-contained statements, definitions, TeX, sources, and Mathlib-leaf metadata), duplicate-node searches, and new-node edge-case checks are vacuous. PASS.
- Edge cases and sources: checked empty Z/U/F, zero and noninvertible coefficient maps, one point component, n=1, and the m=0 boundary (generic clause only); no argument assumes invertibility or silently extends the m≥1 point theorem. No SGA 4/4½ source, Lean file, or compiler/build was used. PASS.

Changes in this second reading: added this review section only. The item, unit binding, citations, search log, and retained repair text were already correct against the current DAG; no node or proof step required alteration.
