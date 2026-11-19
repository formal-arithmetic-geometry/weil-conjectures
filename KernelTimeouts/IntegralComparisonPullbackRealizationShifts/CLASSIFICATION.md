# IntegralComparisonPullbackRealizationShifts: exact Kernel site

**Declaration:** `integralComparisonPullbackRealization_commShift`, origin
`b400b43ec29`.

## Phase gate and top-down bisect

The type-only probe is 7.80 s. The full Before is 105.67 s in the synchronous
Kernel gate versus 11.11 s with Kernel skipped. `probes/AfterIntroSorry.lean`
stops after `commShift_of_localization ...; intro P m; sorry` and takes 7.90 s.
Adding the explicit `change` statement takes 86.06 s; retaining all later
proofs but replacing the final `cancel_shift_square` takes 105.47 s. Thus the
first expensive operation is the conversion created by `change`, before any
normalization, localized shift square, or final cancellation witness.

## Exact expressions

Before `change`, the goal is a morphism equation at
`(integralOperationsGoodLocalization ...).obj P`, with
`M.realization.hom.app` and the derived pullback comm-shift. After `change`,
the same equation is stated at `DerivedCategory.Q.obj P.obj` and uses
`integralDerivedPullback`, `SY.reduction ⋙ H`, and explicit shift functors.
The compact probes print both forms. The endpoint objects are mathematically
the same but are represented through the localization wrapper versus its
underlying `DerivedCategory.Q` object; the conversion unfolds concrete
`PresheafOfModules.obj` and additive/module instances under `NatTrans.app`.

With `-Ddiagnostics=true -Ddiagnostics.threshold=1`, the post-`change`
probe reports 1,193,814 Kernel unfolds of `Add.add`, 1,047,896 of
`PresheafOfModules.obj`, and 812,294 of `AddMonoid.toAdd`. The pre-`change`
probe remains at the 7--8 second import/type floor. These counters identify
the conversion chain triggered by the endpoint representation, not the source
of the mathematics.

## Classification

Primary mechanism: **A**. Contributing mechanisms: **E** and **C**. Evidence:
**confirmed** for the `change` conversion and **strongly supported** for A/E/C.
The fixed wrapper vocabulary keeps the localization endpoint types aligned so
the same square is checked without this conversion.
