1. Files written:
- `dag/nodes/sec-picard-framework/lem-pc-structure-pushforward.json`: statement, no new nodes, Mathlib searches found no match.
- `citations.json`: verbatim citations for both existing proof dependencies.

2. Attachments: none.

3. WANTED: none.

4. The imported proof was checked against the sorry-bearing declaration `AlgebraicGeometry.isIso_pushforwardUnitMap_pullback_snd`, `WeilConjectures/AlgebraicGeometry/Picard/RationalPoint.lean:53-65`, and its docstring. The Lean declaration is still sorry-bearing, so it cannot be attached as closed. The imported statement is the smooth-projective-curve specialization, while the Lean declaration is more general (proper X with `GlobalSectionsBijective`); the specialization is mathematically consistent, and the discrepancy is recorded for lead review rather than silently changing the target. No new node was created because the proof uses only the existing finite-support and flat-base-change statements.

## Second reading by E1
Step 1 checked against the blueprint proof node `lem-pc-structure-pushforward` and the statements of `lem-pc-finite-support-hi` and `lem-sc-flat-base-change-coherent`; verdict: consistent with the unit route. Properness and its base-change stability were checked against the source setup and used to supply the quasi-compact/quasi-separated hypotheses for finite-support quasi-coherence. The affine calculation is the `i=0`, `\\mathcal F=\\mathcal O_X`, `k'=A` specialization of flat base change, with localization compatibility checked on `A\\to A_f`.
The sole item node was checked for B1-B7: it is statement-only, self-contained with its base-change and morphism-convention dependencies, and has no new-node form issues. No new node exists, so there are no new-node statements or duplicate-node searches to repair; the recorded Mathlib searches remain valid and found no exact pushforward theorem. Edge cases checked: `T=Spec(k)`, `T=Spec(A)`, `X=\\varnothing`, `X=Spec(k)`, and `X=\\mathbf P^1_k`.
Changes made: no cross-unit dependency was retained after route review; the existing two citations and unit-local proof route remain unchanged.

## Review by E1
I read the item source blueprint node and the Lean declaration/docstring. Step 1 uses `lem-pc-finite-support-hi` only for the cited conclusion that the direct image of the quasi-coherent structure sheaf is quasi-coherent; that node states exactly this in clause (1). It uses `lem-sc-flat-base-change-coherent` for the displayed base-change isomorphism; that node states `H^i(X_{k'}, F_{k'}) ≅ H^i(X,F) ⊗_k k'`, which specializes at i=0, `F=O_X`, and `k'=A`. Properness of the curve and flatness of `k -> A` are part of the source hypotheses/definitions and the affine localization argument is elementary once the cited statements are applied. The equality `k ⊗_k A = A` and compatibility under `A -> A_f` are direct tensor/localization identities. I checked the edge cases `T = Spec(k)`, `T = Spec(A)` affine, and `X = P^1_k`, where the computed sections are respectively `k`, `A`, and `A`. Existing DAG searches found no duplicate statement or stronger node to cite, and the required LeanFinder, Loogle, and Mathlib grep searches (including a second phrasing) found no Mathlib theorem stating this pushforward result.
