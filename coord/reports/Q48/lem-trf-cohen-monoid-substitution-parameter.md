# Delivery report

1. **Files written.**
   - `dag/nodes/sec-trace-formula/lem-trf-cohen-monoid-substitution-parameter.json`: statement split into six proof steps; Mathlib searches retained and refreshed; no new nodes.
   - `citations.json`: ten verbatim statement quotes for the cited existing nodes.
   - No additional DAG node was created.

2. **Attachments.** None. I found no sorry-free declaration in the project Lean source or in the slopmaster2 source that states this item exactly.

3. **WANTED.** None. The cited ILO paper and Stacks source are present locally.

4. **What was wrong or corrected.** The imported item was unsplit and its `proof_origin` was null. I retained its statement and dependencies, supplied an agent proof, and changed its `status` to `split`. The proof makes explicit the quotient (E'=E_*/(t)), the reduction (E'/pE'), the completion quotient, the finite-adic substitution maps, and the augmentation; it does not silently remove the allowed linear (t_i)-terms. The imported source phrase “θ is congruent to (p)” is used in the precise ideal-membership form stated by the item. The blueprint ancestor is `lem-trf-local-term-locality`, with the local-model route through `lem-trf-formal-monoid-extension-model`; this item is the independent commutative-algebra verification of ILO VI 1.6(ii), not a restatement of the local-term conclusion.

5. **What remains unfinished.** No unfinished work remains in this split. The item still depends on existing unsplit algebra nodes where those nodes are the needed black-box inputs; those dependencies are recorded in the proof and in `split_report.tool_uses`.

## Review by Q48

I read the imported item, the chapter `sec-trace-formula`, unit `sk-i-curve-zero`, the latest blueprint files for `lem-trf-local-term-locality` and the unit, and the source discussion ILO VI 1.6(ii), printed p. 70. I also inspected every cited node's statement. Step 1 uses the existing power-series Cohen regularity, regular-local localization, polynomial regularity, and localization-of-regular-ring statements to establish regularity of the Laurent polynomial local rings. Step 2 checks the explicit quotient by the old variables and the reduction modulo (p), including the needed nonzeroness of (p); it uses only the Cohen-ring statement and elementary localization calculations. Step 3 applies the existing regular-local quotient generator statement to (pE'), and verifies its hypotheses from the preceding steps, yielding (p\notin\mathfrak m'^2). Step 4 uses the existing completion-of-a-quotient, completion-local-ring, and module-completion statements to transport the cotangent class to (D/(t)D\cong\widehat{E'}). Step 5 constructs the substitution from compatible maps on finite adic quotients and checks multiplicativity, continuity, and the augmentation using the displayed monoid hypotheses. Step 6 expands the given ideal-membership relation, applies the augmentation, and checks that the image of (areta) is (p) modulo (t) and cannot lie in (mathfrak m_D^2); it explicitly covers (n=0) and (	heta=p-t_1). Every non-elementary input in the steps is named in `uses`, and each citation quote is copied verbatim from that node's statement in `citations.json`. I checked for cycles and for duplicate or Mathlib replacements before writing; no new node was needed.

I also corrected inherited TeX overescaping and literal newline escapes in the statement, without changing any mathematical assertion, and checked the new proof text uses single TeX escapes. All six steps are below 2000 characters. The first server DAG check and full dry-run preflight passed; the final delivery reruns preflight after this rendering correction.
