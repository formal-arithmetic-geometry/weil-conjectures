# MDA: IntegralComparisonPullbackRealizationShifts

Case: `IntegralComparisonPullbackRealizationShifts`; Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; measurement import pin
`105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`. Source declaration:
`WeilConjectures.integralComparisonPullbackRealization_commShift`.
The immutable diagnostic probe is `probes/mprwe/Original.lean`; its two
roots (177,071 and 235,750 calls) are not the full expensive source root.
The historical full-source aggregate is retained in `EXPERIMENTS-MPRWE.md`
(9,426,198 calls; round 4 supersedes earlier rounds). A fresh field-aware
replay of the immutable aligned-prefix source
`probes/anatomy/aligned-prefix-after-change.lean` (SHA256
`93b29e9f3d03a05f5ffb94167b2d3d351298d142bfed0fae05e422fa73874bc4`)
reached the corresponding
9,426,253-call `change` conversion with root serial 24513. Reduced selected
and aggregate data is in `mda/selected-root.jsonl.gz`.

## 4.1 Gateway-to-cost

The fresh aligned-prefix root is the explicit `change` conversion after
`commShift_of_localization` and `intro P m`: 9,426,253 calls, depth 183,
139,130.382 ms comparison-exclusive and 31,468.013 ms reduction-exclusive;
M1 6,680,881 calls / 137,496.915 ms, M2 25,204 / 1,348.893 ms,
Matched 2,720,167 / 241.294 ms. The source/API first divergence is the complete dependent equation
with `integralTowerHasDerivedCategory` versus
`integralOperationsCommHasDerivedCategory`; the provider-only alignment
retains 9.426M calls and is a negative control.

| Gateway ID | Parent M0 path | Kernel branch / component | Exact child pair | Source/API candidate | M1 subtree calls | Subtree exclusive ms | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| `24513:68` | explicit `change` after `P,m` | application / `argument[2]` | `mda_top(24513,68).left_expr/right_expr`, `CategoryStruct.comp` / `CategoryStruct.comp` | dependent endpoint composition | 6,680,850 | 139,003.851 inclusive | S: fresh selected pair |
| `24513:69` | same | lazy delta / `argument[7]` | `mda_top(24513,69).left_expr/right_expr`, `NatTrans.app` / `NatTrans.app` | nested natural-transformation application | 6,680,835 | 138,983.009 inclusive | S: fresh selected pair |
| `24513:70` | same | second WHNF / Iota | `mda_top(24513,70).left_expr/right_expr`, `CategoryStruct.comp` / `CategoryStruct.comp` | repeated composition head | 6,680,835 | 138,908.194 inclusive | S: fresh selected pair |
| `24513:73` | same | lazy delta / `argument[7]` | `mda_top(24513,73).left_expr/right_expr`, `NatTrans.app` / `NatTrans.app` | second endpoint-app branch | 3,326,676 | 81,423.905 inclusive | S: fresh selected pair |

The fresh parent-child rows identify the first selected expensive object-level
gateway as `CategoryStruct.comp` -> lazy-delta `NatTrans.app` at calls 68-69.
Direct M1 groups are 1,939,882 projection calls / 34,756.262 ms,
481,400 second-WHNF calls / 27,014.786 ms, 1,258,058 application
function-head calls / 9,302.795 ms, and 167,994 proposition calls /
3,232.628 ms. Selected subtree times overlap; direct groups partition cost.
All these aggregate groups have `source=unknown`, so their direct time belongs
to the branch/component, not to a specific named declaration.

## 4.2 Definition/API path

| Candidate | Role | First seen | Kernel path | M1 calls | M1 exclusive ms | Intervention / evidence |
| --- | --- | --- | --- | ---: | ---: | --- |
| `integralTowerHasDerivedCategory` vs `integralOperationsCommHasDerivedCategory` | producer candidate | S0/S2 `change` target | dependent object type | included in root | included in root | Provider alignment leaves 9.426M calls: N as amplifier cause |
| Localized endpoint wrapper | gateway/boundary candidate | before explicit `change` | endpoint API | not separately isolated | not separately isolated | Prefix is about 6.20 s; full `change` about 88.56 s: S boundary, broader counterfactual |
| `PresheafOfModules.proj` | amplifier/path node | fresh selected path | projection | not declaration-isolated | not declaration-isolated | P: downstream path |
| `SubNegMonoid.toAddMonoid` / additive projections | amplifier/path nodes | fresh selected path | field/projection | not declaration-isolated | not declaration-isolated | P: downstream |
| `CategoryTheory.NatTrans.app` | gateway/path node | `24513:69`, `24513:71`, `24513:73` | lazy delta / argument | 7,697 component-group calls | 10,465.324 component-group ms | S for gateway, U for declaration-specific direct cost |
| `CategoryTheory.Functor.obj` / `HomologicalComplex.mk` | amplifier/path node | fresh selected Expr path | WHNF/object path | not declaration-isolated | not declaration-isolated | P |

The prior provider-only control is retained exactly: it changes all target
provider leaves while preserving the consumer and dependent telescope, but
the aligned-prefix root remains 9,426,253 calls. The unavailable copied instance-alignment
probe also lacked `HeadAuditTools.olean`; no new control claim is made.

## 4.3 Root-to-source chain

Source writes an explicit `change` after the localized comparison theorem
and instantiates `P,m`
-> complete dependent category-morphism equation uses two derived-category
provider routes
-> first S2 divergence is the provider leaf, with larger endpoint/object
arguments differing beneath it
-> Kernel enters `CategoryStruct.comp` at call 68 and lazy-delta
`NatTrans.app` at call 69
-> repeated WHNF/composition plus downstream `Functor.obj` and additive
projection paths amplify the M1 workload
-> provider alignment changes the first leaf but not the workload
-> keeping the localized endpoint wrapper avoids the explicit conversion and
is the best available API-level boundary (S/P, not an M0-preserving cut).

## 4.4 Summary and controls

| Producer | Expansion gateway | Amplifier | Best one-factor intervention and effect | Evidence |
| --- | --- | --- | --- | --- |
| Complete dependent endpoint/API equation (P); provider leaf is only the first exact difference | `CategoryStruct.comp` -> lazy-delta `NatTrans.app` at fresh calls 68-69 (S) | Direct projection/WHNF/application groups (S); specific `PresheafOfModules.proj` and additive definitions (P) | Provider-only alignment leaves 9.426M calls (N). Localized endpoint wrapper reduces the broader proof path to the prefix floor but changes the API obligation (S, API counterfactual) | Fresh root 24513 MDA validation plus historical MPRWE/CCMOA |

Boundary status: localized endpoint wrapper is fragile but effective; writing
the explicit `DerivedCategory.Q` target punctures it. Finalization causality is
unknown because no pre-finalization expression is available. A future focused
run can resolve the exact source declaration behind the long `unknown` groups.
It needs source attribution that follows the selected Expr path through private
declarations and assigns direct cost to the owning call, rather than using
the current nearest-prefix fallback.

## Audit note

The provider leaf is **N** as a sufficient cause: changing it leaves the
9.426M-call root. The `CategoryStruct.comp`/`NatTrans.app` path is **S** as
observed traversal, but named projection owners are **P**. The endpoint
wrapper is an API-level counterfactual; its broader proof obligations prevent
promotion of a single gateway or producer to D.
