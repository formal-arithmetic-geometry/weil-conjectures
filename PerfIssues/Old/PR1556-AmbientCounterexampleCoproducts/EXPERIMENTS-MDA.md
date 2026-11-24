# Mismatch-to-definition attribution: PR1556

## A. Root and evidence boundary

The pinned `probes/mprwe/OriginalNatTrans.lean` (SHA-256 `4f4dec7cc0fb23ef057568f9fe3d6abfc275de8a7510f7cda76d0b9fb2843f79`) replays the generated congruence proposition domain. Lean 4.35.0 and the current import pin are in the shared MDA contract; they do not establish the historical PR's S2 source. The selected Eq/Eq root has a matched function head. The exact historical S5 replay in `ccmoa/snapshot.log` locates a concrete `commShiftIso.hom.app` premise against the generated congruence domain. Historical S1/S2 and pre-finalization Exprs remain unavailable.

Fresh MDA root `6006` succeeds: 6,670,198 calls, 184,293.573 ms comparison-exclusive; M1 5,006,059 calls/183,100.909 ms, M2 9,121/1,021.200 ms, Matched 1,655,017/122.428 ms. M1 median/max depth is 122/213 and mean fan-out 1.330. Exact serialization materially inflates these trace times, so the saved paired direct checks measure intervention effects.

## B. Gateway-to-cost (§4.1)

`mda/pair-<call>.json.gz` contains the exact structural pair, including hidden arguments. Inclusive all-label subtree ms overlap and must not be summed. The direct M1 column is the additive branch/component group total across the root.

| Gateway ID | Parent M0 path | Kernel branch / exact child pair | Source/API candidate | Subtree M1 calls | Inclusive subtree ms | Direct M1 ms, branch/component | Evidence |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| 6006:4 | root Eq argument | `application/argument[1]`; `CategoryStruct.comp` / same, **M2 entry** | concrete composition side | 5,006,058 | 184,244.532 | application argument[1]: 13,766.413 | S |
| 6006:6 | call 5 | `second_whnf`; `Equiv.toFun` / same, M1 | equivalence exposure | 5,006,058 | 183,468.124 | second_whnf: 89,082.328 | S |
| 6006:13 | call 12 | `lazy_delta/argument[7]`; `DFunLike.coe` / same, M1 | nested `NatTrans.app` premise | 4,012,034 | 173,745.765 | lazy_delta argument[7]: 4,715.552 | S |
| 6006:39 | call 13 | `application/argument[0]`; `NatTrans.app` / same, M1 | concrete comm-shift component | 4,012,022 | 173,647.956 | application argument[0]: 14,647.570 | S |
| 6006:61 | call 60 | `lazy_delta/argument[7]`; `DFunLike.coe` / same, M1 | repeated major-premise projection | 3,926,393 | 168,765.508 | lazy_delta argument[7] as above | S |

The root-side `CategoryStruct.comp` child is M2 at call 4, but its descendant call 6 is M1 and carries nearly all root M1 work. This keeps the sibling/new-mismatch entry distinct from inherited M1 propagation. The mapped accessors are `CategoryStruct.comp` field 2, `NatTrans.app` field 0, and `Equiv.toFun` field 0. Projection groups contribute 1,289,100 M1 calls and 29,603.340 ms direct M1 time. The exact pair files show `EquivLike.coe`, `Equiv.toFun`, `DFunLike.coe`, and nested `NatTrans.app`; `Equiv.proj`/`equivShrink` are downstream projection path nodes. No separate full cost is charged to each nested node.

## C. Definition/API path (§4.2) and chain (§4.3)

| Candidate | Role | First seen | Kernel path and cost | Intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| Concrete `commShiftIso.hom.app` vs generated congruence domain | producer | S0 source, exact S5 pair | root Eq/Eq, first relevant major-premise difference | argument-6 alignment | S; historical S2 U |
| `CategoryStruct.comp` -> `EquivLike.coe` / `Equiv.toFun` | first gateway | calls 4-6 | call 6 contains 5,006,058 M1 descendants, 183,468.124 ms inclusive | whole-equality cancellation avoids path | S |
| `DFunLike.coe` -> nested `NatTrans.app` | amplifier/gateway continuation | calls 13/39 | 4,012,034 M1 descendants at call 13; 173,745.765 ms inclusive | argument-6 alignment removes root | S |
| `Equiv.proj`, `equivShrink` | downstream amplifier | projection descendants | 29,603.340 ms direct M1 projection group | no isolated field control | P |

Source concrete component proof -> generated Eq/Eq domain with distinct NatTrans major premise -> root M0 -> composition argument call 4 (M2) -> equivalence WHNF call 6 (M1) -> `DFunLike.coe` call 13 -> nested `NatTrans.app` call 39 -> projection chains -> 5,006,059 M1 calls/183,100.909 ms M1 exclusive. The first source-to-S5 link is supported by the saved replay; the historical elaboration step is unknown.

## D. Intervention and E. boundary

The saved localized direct check aligns only outer `NatTrans.app` argument 6, retaining the checked result type and other arguments: 51,229 ms original -> below timer resolution aligned -> 53,273 ms restored. This is a one-factor **API-level counterfactual**; it removes M0 and is not an M0-preserving subtree cut. The same-statement whole-equality cancellation proof lowers whole-prefix user CPU from 59.47 s to 4.75 s, but changes the proof strategy. It is the effective boundary; restoring the concrete component `simpa` proof punctures it. Status: fragile but effective. No valid descendant-only replacement has been shown under the original dependent type.

## Summary row (§4.4)

| Case | Producer | Gateway | Amplifier | Best one-factor intervention/effect | Levels |
| --- | --- | --- | --- | --- | --- |
| PR1556 | concrete comm-shift component vs generated congruence premise | composition argument then equivalence WHNF | nested `NatTrans.app`, `DFunLike.coe`, equivalence projections | argument-6 alignment: 51,229 ms -> below resolution; restoration 53,273 ms | producer S; gateway S; amplifier S/P; boundary S |

The shared tool's `source` tag is `unknown` in the selected rows; it does not prove authored ownership. Historical S2/pre-finalization provenance remains U. A field-tagged full M1 direct-cost stream, rather than only selected top pairs, would be needed to split the 29,603.340 ms projection group among `Equiv.proj` and `equivShrink` without double-counting.

## Audit note

The component mismatch and restoration are **S**: historical S5 and the aligned/restored timings exist, but S2 is unavailable. Argument-6 alignment changes M0 and is an API-level counterfactual, not a local subtree cut. Projection field ownership remains **P/U**.
