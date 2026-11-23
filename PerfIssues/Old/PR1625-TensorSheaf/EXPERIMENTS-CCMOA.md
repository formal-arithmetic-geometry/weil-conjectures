# CCMOA: PR1625 TensorSheaf

## Stage audit
- S0: Before supplies Functor.leftDerived2NatTrans_app_app directly to a theorem stated with two nested .app projections of leftDerivedUpperStarTensorComparison. After proves equality of the whole natural transformations by rfl, rewrites once, then applies the component lemma. This is an explicit source/API representation choice.
- S1: The old source syntax contains notation and projections, but no macro-expanded historical snapshot was retained; macro causality is Unknown.
- S2: No valid historical pre-finalization Expr snapshot is available. The new scratch replay fails in preceding declarations against the permitted current closure, so its partial terms are excluded.
- S3: Historical pre-finalization data are unavailable. No finalization cause is inferred.
- S4: Earlier imported-value inspection established NatTrans.app and CategoryStruct.comp as abbrev field accessors; their immediate bodies expose NatTrans.0 and CategoryStruct.2 projections. No complete old ConstantInfo dump or auxiliary inventory was retained.
- S5: The earlier exact check opens 15 binders and compares the inferred body type with the declared result, both Eq-headed. The expensive left CategoryStruct.comp pair (93.679 s) reaches an outer NatTrans.app pair (96.236 s); its first significant structural mismatch is major argument 6, a nested NatTrans.app pair (95.717 s). The older probe did not serialize full Expr paths/hashes or the entire local context.
- S6: Projection and dependent descent expose the differing concrete major premise. READY4.2 root 65966 has 11,757,788 calls; M1 8,111,028 and 99.546% exclusive time, M2 4,686, Matched 3,642,041. The earliest representation difference is visible at S0; the exact elaborated mismatch is established only at the older S5 audit.

## Representation control
The existing type-preserving major-premise control changes only outer NatTrans.app argument 6 to the definitionally equal left premise; its result type remains structurally identical. The direct pair changes 95.869 s to 0 ms, and reverse restoration takes 93.567 s. This is a valid localized Expr change but has no READY4.2 after-counter or fresh structural dump. The same-statement whole-transformation source control lowers target Kernel checking from 87.6 s to 2.43 s, but changes proof construction and is not a strict one-factor root control. Evidence is Strongly supported, not Demonstrated under the CCMOA rule.

C was not run: no valid S2 snapshot identifies a hidden instance, coercion, or transparency choice. D was not run: no accessible pre-finalization term or S2/S4 discrepancy.

## Boundary inventory
The outer head of the slow path is nested NatTrans.app (abbrev), below CategoryStruct.comp (abbrev); both expose projections. The fast proof establishes a whole NatTrans equality before taking components, so the concrete nested projection pair is not checked at that point. Direct component proof application in Before punctures the boundary and restores the large conversion. Status: fragile but effective. A future refactor that replaces the whole-transformation equality with direct nested .app reasoning carries this risk.

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| PR1625 | S0 representation; exact pair at S5 (Strongly supported) | Direct nested component/API choice (Strongly supported) | Unknown | Unknown | Projection descent (Strongly supported) | Whole NatTrans equality (Strongly supported) | Fragile but effective (Strongly supported) |

Raw evidence: ccmoa/snapshot-attempt.log records the failed current-closure replay and is not an Expr snapshot. Historical evidence: HEAD-AUDIT.md, EXPERIMENTS-AD.md, EXPERIMENTS-M1P.md, Before.lean/After.lean.
