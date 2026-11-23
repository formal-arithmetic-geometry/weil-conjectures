# CCMOA report: IntegralComparisonPullbackRealizationShifts

Case: `KernelTimeouts/IntegralComparisonPullbackRealizationShifts`  
Declaration: `integralComparisonPullbackRealization_commShift`  
Root: the explicit `change` after `commShift_of_localization` and `intro P m`.
The records below reuse the existing AD/IM/M1P/MPRWE probes and READY4.2
counters; the earlier local-instance edit is treated as a negative control and
is not repeated.

## A. Stage snapshots

The helper domain is the explicit target after `P` and `m` have been
instantiated. The comparison is therefore between the complete dependent
category-morphism equations, not a generic `HasDerivedCategory` binder.

| Stage | Snapshot and result |
| --- | --- |
| S0 | Source calls `commShift_of_localization`, introduces `P m`, then writes an explicit `change` target. The target uses `integralDerivedPullback`, `DerivedCategory.Q.obj P.obj`, and the operations-comm reduction path. |
| S1 | The target contains ordinary applications and category notation; macro expansion does not introduce a different provider choice. |
| S2 | Under `Eq` -> `Quiver.Hom` -> `Functor.obj` -> `DerivedCategory`, the actual goal contains `integralTowerHasDerivedCategory` while the proposed target contains `integralOperationsCommHasDerivedCategory`, repeated on all three composite sides. Both are regular definitions of height 28. The first exact instance leaf is therefore an elaborated argument in the dependent object type. |
| S3 | The imported declaration has no accessible pre-finalization term. The declaration-finalization record is observational-only; no generated proof field is on the first divergent path. |
| S4 | The two first-leaf constants are regular height-28 definitions with lambda bodies. The aligned downstream pair additionally exposes `ObjectProperty.FullSubcategory` versus `CochainComplex`; `integralTowerModules` is an abbrev while `scalarReductionSource` is regular height 28 in the shift-functor argument. |
| S5 | READY4.2 original downstream root: 9,426,253 calls, depth 183, 44,602.554 ms comparison-exclusive, 28,664.202 ms reduction-exclusive, 28,206,595 WHNF calls. The root conversion succeeds but is expensive. |
| S6 | The conversion descends through `PresheafOfModules.obj`, additive structure projections, `CategoryStruct.comp`, and nested `NatTrans.app`. READY3.2 attribution is M1 9,275,312 calls / 98.400%, M2 125,250 / 1.328%, matched 25,636 / 0.272%. The first instance leaf is not the dominant timed child. |

**First divergence.** The source/API target is visible at S0, while the first
exact provider split is S2. It is active in the `change` conversion; the
Kernel then exposes a deeper functor/object representation.

## B. One-factor representation control

`align_instance_change` replaces only each target occurrence of
`integralOperationsCommHasDerivedCategory` with the corresponding actual
`integralTowerHasDerivedCategory` expression. The consumer, expected
equation, dependent telescope, preceding arguments, and local context remain
the same. This is the corrected control; the older `LocalTowerInstance`
source edit did not change the elaborated pair and is not evidence.

| Variant | Expr change | READY4.2 root result |
| --- | --- | --- |
| Original | First instance leaf is `integralTowerHasDerivedCategory` vs `integralOperationsCommHasDerivedCategory`; downstream object arguments also differ | 9,426,253 calls; 44,602.554 ms comparison; 28,664.202 ms reduction |
| Instance-aligned | All corresponding target instance leaves replaced with actual leaves; first remaining difference moves to `ObjectProperty.FullSubcategory` vs `CochainComplex` under `Functor.obj` | 9,426,253 calls; 44,446.676 ms comparison; 28,410.084 ms reduction |
| Restored | Original target representation restored | 9,426,237 calls; 44,551.528 ms comparison; 28,555.918 ms reduction |
| Kernel-skip diagnostic | Same aligned Expr, `debug.skipKernelTC true` | 4.20 s wall; diagnostic only, no Kernel proof claim |

The fresh release diagnostics are 83.65 s original and 83.15 s aligned; the
READY4.2 counter runs above have the same 9.426M-call tree. The instance edit
changes the elaborated pair and preserves the root obligation, but leaves the
Kernel workload unchanged within run noise. It is a valid negative control,
not causal evidence for the instance leaf.

## C. Targeted elaborator provenance

The relevant decision is instance synthesis for the `DerivedCategory` object
type. The aligned probe records the selected constants and all three
occurrences. The earlier local instance declaration is a no-op: its S2 pair
and cost are unchanged. The corrected control changes the stored argument but
does not change calls or the downstream category-object pair. No alternate
metavariable assignment or transparency mode was shown to change the final
Expr and workload together.

Result: an Elaborator-selected provider is **Strongly supported** as the
first representation difference, but Elaborator causality is **Not observed**.
No D audit is indicated beyond the imported finalization-observable-only
record.

## D. Cheap-but-fragile boundary inventory (E)

| Boundary | Current behavior | Puncture and risk | Status |
| --- | --- | --- | --- |
| Localized endpoint wrapper | The localization wrapper keeps the pre-`change` endpoint compact and cheap (about the 7--8 s import/type floor). | Writing the explicit `DerivedCategory.Q` target forces the dependent object conversion. | Fragile but effective |
| Shared `HasDerivedCategory` provider | Aligning the provider moves the first path without reducing the root. | Independently reconstructing the provider or changing category wrappers exposes the next `Functor.obj` and module structure. | Fragile but effective |
| Named module heads | `integralTowerModules` is abbrev while `scalarReductionSource` is regular height 28. | Unfolding or changing declaration kind can expose module/additive proof data. | Untested |
| Whole dependent equation | The full equation is currently accepted after recursive comparison. | Mixing raw and wrapper vocabulary, or inlining `NatTrans.app` composites, can re-enter the deep path. | Untested |

## Synthesis row

| Case | Earliest divergence stage | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| IntegralComparison | S0 target choice; exact provider leaf S2 (**Demonstrated**) | Dependent wrapper/API plus `HasDerivedCategory` instance path (**Plausible**) | Not observed | Not observed | Strongly supported | Localized endpoint wrapper and shared provider alignment (**Strongly supported**) | Fragile but effective (**Plausible**) |

The exact first leaf and changed Expr are **Demonstrated** observations. The
instance leaf's causal sufficiency is only **Plausible** and is contradicted by
the same-root negative control; the downstream `Functor.obj`/module path is
**Strongly supported** as the effective Kernel boundary.
