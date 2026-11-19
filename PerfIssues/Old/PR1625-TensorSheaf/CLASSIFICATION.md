# PR #1625 component classification

Case ID: `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac`, on Lean 4.35.0 at master revision `1ef1fddac73e`. [Before.lean](Before.lean) restores the old direct term; [After.lean](After.lean) uses the current preliminary equality of natural transformations. Both preserve the current prefix and stop after the target.

## Phase and cost site

The old proof is a bare application of `Functor.leftDerived₂NatTrans_app_app` to concrete derived comparison data. Its Kernel type check takes 87.6 seconds, versus 2.43 seconds after the fix. Whole-prefix user CPU is 188.18 versus 104.15 seconds and peak RSS is 8,245,292 versus 2,929,672 KB. Tactic execution totals 5.55 versus 5.96 seconds. The cost is Kernel conversion while checking the target proof term, not the source-level `exact` tactic. The earlier fixed proof in this file still contributes about 15.4 seconds of Kernel checking to both variants.

## Mechanism

Primary label: **A, reduction/definitional equality**, with **E, representation mismatch**, contributing. The old term makes the Kernel reconcile `((Functor.leftDerived₂NatTrans ...).app _).app _` with `((leftDerivedUpperStarTensorComparison A g).app _).app _` below two `NatTrans.app` projections. The [historical PR diagnosis](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1625) identifies that conversion pair. The fixed proof first establishes equality of the whole natural transformations by `rfl`, rewrites with it, then applies the same component lemma. On 4.35.0 this source-level control removes 85 seconds from the target Kernel check.

The pair under `NatTrans.app` is documented by the historical PR; a fresh Kernel expression dump for this exact 4.35.0 proof was not made. Confidence is high for phase, declaration, and proof-value cost, and moderate for the inner conversion mechanism. This entry covers the component lemma only, not the PR's other changed proof.
