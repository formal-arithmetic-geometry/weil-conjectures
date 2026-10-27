# Stage-1 report: lem-sfb-accelerated-finite-field-cochain-differences

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-accelerated-finite-field-cochain-differences.json — item, statement, split; no exact Mathlib match. Statement unchanged. Six proof steps, every non-elementary input supplied by an existing node; rebased on the current DAG for the promotion return.
- citations.json — five verbatim statement excerpts, one for each citation in the proof.
- searches.jsonl — five actual Q51 searches, with returned results inspected; the inherited Q49 searches remain unchanged in the item's mathlib_searches.
- report.md — this report. The sandbox-only write_split.py is a reproducible authoring helper, not a delivery node or a patched project tool.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched lean/WeilConjectures for the exact item id and for finite-subfield, contractive-projection and retraction terminology. The finite-field occurrences concern finite characteristic fields, derivations or Frobenius; none states this analytic cochain result. There is no finished declaration to attach.

## WANTED

WANTED: a human-written reference for simultaneous accelerated finite-subfield approximation of continuous compact parameter families in the completed algebraic closure of Q_ell, including the exact eventual vanishing of successive differences on algebraic-valued cochains, for lem-sfb-accelerated-finite-field-cochain-differences. The blueprint paragraph does not assert this analytic result. The supplied proof is expressly agent-written. No SGA source is used.

## Findings and corrections

The imported statement is consistent and is retained verbatim; there is no STATEMENT-DISPUTED issue. Its source names old proof steps 7–10, but its own proof was empty. I supplied the argument with existing DAG inputs rather than introducing copies of them. In particular the existing weaker continuous retraction lemma would not justify the uniform norm estimates, so the proof uses lem-sfb-norm-one-finite-subfield-projection instead.

I read AGENTS.md, the stage-1 brief, stage 1, the worker role, GOAL.md, the three blueprint levels in SETUP.md, the chapter and unit records, the current direct-images proof paragraph (3), and both copies of delivery-errors.md sections B–E. The unit record is an older sec-six-functors record, whereas the item's current source is sec-six-functors-basics. I keep the item's chapter/unit metadata and use the current source paragraph; the analytic work remains below its open direct-image clause. No unit or chapter file is changed. blueprint_refs.py ancestor reports None; the inherited null ancestor is retained rather than inventing one. The report identifies the current blueprint place explicitly.

## Not duplicates

No new nodes were created. The existing norm-one projection, dense extension, finite-extension completeness, metric field completion and compact-product nodes supply all analytic and topological inputs. Whole-blueprint searches for contractive projection, contractive, accelerated, finite product compact, and cochain differences returned no blueprint statement equal to the item. The DAG searches additionally located the weaker finite-subfield continuous-linear retraction; it is not a substitute for a norm-one map and is not copied.

## Review by Q51

I checked the analytic hypotheses against the actual statements of all five cited nodes, not their proofs. I read the current main-20261015 direct-images proof paragraph (3): it motivates the coefficient analysis but supplies none of the analytic steps, which remain labelled agent work. For the extension ingredient I also read Mathlib/Analysis/Normed/Operator/Extend.lean lines 175–217, including LinearMap.extendOfNorm, agreement on the dense subspace, the preserved norm bound and uniqueness. I read Stacks topology.tex, theorem-tychonov (Tag 08ZU), around lines 2446–2470. No new node needs an additional source review.

Step 1 uses the norm-one projection node's explicit F-linearity, identity on F and pointwise norm bound. Each F_N is finite over Q_ell by hypothesis, so that lemma applies, and its map is Q_ell-linear. The completeness node takes precisely an absolute value extending the given Q_ell one, so it applies to the restriction to F_N without any change of topology. The completion node supplies the injective isometric field embedding. Density is part of the definition of metric completion, not a claim of completeness of Omega. The dense-extension node takes a dense linear subspace, a complete target and a contractive linear map; I verified each of these, giving Q_N on B with the same bound and unchanged restriction. Passing the ultrametric inequality from the dense subspace to B is written explicitly using norm continuity. No alleged contraction from B to all of Omega is used.

Step 2 cites the compact-product node, whose statement allows an arbitrary set of compact factors and therefore the finite products S times G^r here. I use its open-cover definition directly: inverse images of balls with algebraic centers cover each domain by density, and a finite subcover gives finitely many centers, all inside one F_M. The displayed estimate uses that Q_N fixes those centers for EVERY N at least M; this supplies a tail estimate, not just one good projection. Both domains are compact and both cochains are continuous. The finite-cover bound also shows all the suprema used exist as finite real suprema. This is one routine finite-cover argument, not a new approximation theorem assumed without proof.

Step 3 makes the tail indices dominate the finite prescribed list and the preceding index plus one. D_t is finite and positive, so no division by zero occurs even if C_j is unbounded as j varies or the N_j are not monotone. Step 4 checks every coefficient of the written differential is rational, so its finite sum commutes with the chosen linear maps. It proves the equations on actual cochains. Increasing fields contain both summands of each difference, including the special zero map at index -1. Step 5 uses the ultrametric maximum, not an ordinary sum estimate, and checks the direction of the D_{i+1} versus D_i inequality. It asserts bounds only for i at least 1, as required, and uses finite telescoping sums before taking the uniform limit.

Step 6 distinguishes exact eventual fixing of algebraic values from convergence of completed values. For a fixed z-value in F_M, i at least M+1 ensures BOTH neighboring projections fix it. For j at most i, the index bound at i-1 covers N_j, including the boundary case i=j=1 through L_0 at least N_1. Substituting the homogeneous formula commutes with the coefficient maps pointwise. No topological condition on R is introduced and no vanishing assertion is made for completed-valued c_i.

I tested the small cases: S a point, G trivial, z=b=0, n=2, i=0, the first difference i=1, constant algebraic z-values, constant completed values outside Omega, N_j arbitrarily out of order, C_j=1, and rapidly growing C_j. The index and error bounds survive each case; the initial term needs no smallness bound. The proof assumes no group action beyond the stated trivial one. Every proof step is below 2000 characters. I checked B1–B10, C1–C8, D1–D5 and E1–E7: no new underspecified statements, no unsupported theorem citation, no clause renamed as a new node, no hypothesis added, no route substitution, and no implicit compatibility argument. citations.json quotes are literal substrings of the live node statements. The graph and route checks are left to the required server dry run as well.

## Unfinished work

None within this stage-1 item. The WANTED reference remains explicit; it does not replace any proof step. Delivery validation and push are recorded by deliver.py.


## Repair of the promotion return (2026-10-23)

The return identifies approved head d3a137cee44 and a landing refusal because the side completion had not been promoted to the live queue DAG. I treated the retained sandbox as that returned work, not as a reason to resplit from scratch. I compared it field by field with the current read-only item: the statement, statement dependencies, source, chapter, unit, created record, and blueprint reference agree; live still has status unsplit, an empty proof, and no repair note. I rebuilt the sandbox node from that current item and overlaid only the retained split fields and searches. The delivery command constructs its commit on the freshly fetched origin/sheaf-dag, so it supplies the actual delivery rebase without a worker git command.

I reread every current proof dependency in full at the statement level: lem-sfb-norm-one-finite-subfield-projection, lem-weil-l-adic-extension-complete, lem-sfb-normed-field-completion, lem-sfb-dense-subspace-contractive-extension, and lem-weil-pbc-tychonoff-product-quasi-compact. None is merged or missing. The projection input now records Q91's repaired four-step proof, including the corrected norm-axiom verification and the admissible-values extension inputs. Its statement still supplies precisely the F-linear retraction and norm bound used by step 1; this delivery uses that statement and does not import its proof dependencies. The four other current statements still give finite-extension completeness, an isometric completion field embedding, contractive dense extension, and compact products, respectively. No citation needs redirecting.

The substantive clarification in the delivered proof is in step 1: multiplicativity of the completion norm explicitly verifies the scalar-norm identity on B and F_N, so the normed-vector-space hypotheses of the dense-extension statement are discharged before it is applied. I also expanded the compact-product quote in citations.json to the entire current statement, including the quasi-compactness conclusion. All five citations are verbatim current statement substrings, and their step numbers agree with the proof. The statement and all six inherited arguments are retained; the logged searches remain unchanged because neither the statement nor the search question changed.

For the renewed self-review I checked each step again. Step 1 uses the finite-dimensional intermediate-field hypothesis for both projection and completeness, identifies Omega isometrically with the dense subspace, and uses the complete target F_N. Step 2 applies the compact-product statement to S and finitely many copies of G; all domains are nonempty because S is nonempty and G contains its identity. Its finite subcover gives a common field index for all centers, so every larger projection fixes them. Steps 3 through 6 are the written finite-max recursion, finite-sum linearity calculation, ultrametric estimate and telescoping identity, and exact fixing of algebraic values. In particular, i=j=1 uses L_0 at least N_1; completed b-values require no eventual fixing. I rechecked zero cochains, trivial G, arbitrary order of N_j and arbitrarily growing C_j. There is no statement dispute or new node. All steps remain below 2000 characters.

I reread the current blueprint direct-images paragraph (3), the current chapter record and older unit record, Mathlib/Analysis/Normed/Operator/Extend.lean:175–217, and Stacks topology.tex at theorem-tychonov (Tag 08ZU). The source still supplies the coefficient-analysis context rather than this analytic theorem, so the inherited agent proof designation and WANTED reference are retained. The initial required dry run completed successfully at d387d4537bd before these clarifications; the final edited version is submitted to a fresh dry run before push.
