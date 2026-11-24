# Mismatch-to-definition attribution: PR1625

## A. Root and source boundary

The pinned `probes/mprwe/OriginalNestedApp.lean` (SHA-256 `708e561cb054dc345156d671666b3c9deb1fa7766e206e41946c99eaebaef5d6`) replays the body-type conversion of `leftDerivedUpperStarTensorComparison_app_app_fac`. Lean 4.35.0 and the pinned current import tree are specified in the shared MDA contract; the original PR's historical S2 and accepted after-counter replay are unavailable. `Before.lean` directly applies `Functor.leftDerived₂NatTrans_app_app` to a statement with two nested `.app` projections. `After.lean` first proves equality of the whole natural transformations by `rfl`, rewrites once, then applies the same component lemma. This is an explicit source/API choice, but the exact historical elaborated producer is known only at the older S5 audit.

The M0 root is Pi/Pi. The dependent `Eq`/`Eq` body is instantiated through binder 15. Earlier exact checks localize the expensive left `CategoryStruct.comp` pair (93.679 s), then outer `NatTrans.app` (96.236 s), then its argument 6, an inner `NatTrans.app` pair (95.717 s). Arguments 0-5 and 7 of the outer `.app` were 0-2 ms each. `NatTrans.app` and `CategoryStruct.comp` are `abbrev` accessors exposing `NatTrans.0` and `CategoryStruct.2` projections. The fresh selected exact pairs retain hidden arguments and universe levels in `mda/pair-<call>.json.gz`.

Fresh MDA root `79312` with one Lean thread succeeds: 11,757,800 calls, 158,646.806 ms comparison-exclusive; M1 8,111,031 calls/153,172.475 ms, M2 4,686/4,523.601 ms, Matched 3,642,050/372.921 ms, Unclassified 32/193.192 ms. M1 median/max depth is 101/125 and mean fan-out 1.448. The 12-call difference from the accepted 11,757,788-call root reflects this replay setting. Trace exclusive time is inflated by exact Expr serialization; saved paired direct checks are used for intervention effects. Additive calls, transition edges, and direct time reconcile in `mda/validation.md`.

## B. Gateway-to-cost (§4.1)

The exact child pair lives in each named `mda/pair-<call>.json.gz`; head names below are locators only. Inclusive all-label subtree time overlaps. Direct M1 group totals are additive over the root and are not charged again to nested selected nodes.

| Gateway ID | Parent M0 path | Kernel branch / exact child pair | Source/API candidate | Subtree M1 calls | Inclusive subtree ms | Direct M1 ms, branch/component | Evidence |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| 79312:2 | Pi/Pi root | `quick/dependent-body[15]`; `Eq` / `Eq`, M1 | instantiated dependent proposition | 8,111,031 | 158,262.189 | 169.049 at body[15] | S |
| 79312:44 | body call 2 | `application/argument[1]`; `CategoryStruct.comp` / same, M1 | left composition side | 8,022,115 | 157,029.412 | application argument[1]: 13,900.454 | S |
| 79312:45 | call 44 | `second_whnf`; `DFunLike.coe` / same, M1 | coercion/projection exposure | 8,022,114 | 155,630.800 | second_whnf: 41,252.430 | S |
| 79312:54 | call 53 | `second_whnf`; localization category `_aux_5` / same, M1 | category instance path | 8,022,106 | 151,631.556 | second_whnf as above | S |
| 79312:93 | call 54 | `lazy_delta/argument[6]`; `DFunLike.coe` / same, M1 | outer `.app` major premise | 8,022,087 | 149,571.862 | lazy_delta argument[6]: 4,565.794 | S |
| 79312:110 | call 96 | `application/argument[0]`; `NatTrans.app` / same, M1 | nested `.app` component | 8,022,075 | 149,350.223 | application argument[0]: 15,076.916 | S |

The dependent-body gateway and its projection descendants are distinct: the former instantiates the original Pi mismatch; the latter repeatedly exposes the concrete natural-transformation premise. The mapped accessors are `CategoryStruct.comp` field 2, `NatTrans.app` field 0, and `Equiv.toFun` field 0. Call 111 is M2 after nested call 110, then call 112 is M1; the M2 entry is not silently counted as M1. Projection groups contribute 1,629,258 M1 calls and 31,046.339 ms direct M1 time. The complete direct-cost partition is in `mda/groups.jsonl.gz`; the selected top pairs are nested and cannot be summed.

## C. Definition/API path (§4.2) and chain (§4.3)

| Candidate | Role | First seen | Kernel path and cost | Intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| Direct nested `.app` API vs whole NatTrans equality | producer | S0 source, exact pair at S5 | outer `NatTrans.app` argument 6 is the first costly component | whole-equality rewrite | S; historical S2 U |
| Pi binder 15 dependent body | gateway | call 2 | 8,111,031 M1 descendants; 169.049 ms direct M1 at this entry | whole equality reorganizes obligation | S |
| `CategoryStruct.comp` and nested `NatTrans.app` projection | gateway/amplifier | calls 44/110 | 8,022,075 M1 descendants at call 110; 149,350.223 ms inclusive all-label | major-premise alignment removes root | S |
| `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun`, `Equiv.proj`, `equivShrink` | downstream amplifier | calls 45-47, 93-96, projection descendants | 41,252.430 ms direct M1 WHNF group; 31,046.339 ms direct M1 projection group | no isolated field control | P |

Source direct component lemma -> nested `.app` sides with distinct concrete major premises -> Pi/Pi M0 -> binder-body[15] call 2 -> Eq/Eq composition call 44 -> outer then inner `NatTrans.app` major premise (call 110 is an inner selected component) -> equivalence/projection descendants -> 8,111,031 M1 calls/153,172.475 ms M1 exclusive -> whole NatTrans equality boundary. The source-to-exact-S5 link is supported by the old component probe; historical S2/elaboration and finalization links remain unknown.

## D. Intervention and E. boundary

The saved one-factor major-premise control replaces only the right outer `NatTrans.app` argument 6 with a definitionally equal left premise; other arguments and the checked result type stay fixed. Its direct check changes 95.869 s original -> below timer resolution aligned -> 93.567 s restored. This is a **root-changing API-level counterfactual** because M0 is removed, not an M0-preserving descendant cut. The same-statement source rewrite to a whole NatTrans equality changes target Kernel checking from 87.6 s to 2.43 s, but alters proof construction. The whole-equality head is a fragile but effective boundary: direct component application in `Before.lean` punctures it and restores the expensive path. A same-M0 child-only intervention has not been constructed under the original dependent telescope.

## Summary row (§4.4)

| Case | Producer | Gateway | Amplifier | Best one-factor intervention/effect | Levels |
| --- | --- | --- | --- | --- | --- |
| PR1625 | direct nested `.app` component vs whole NatTrans API | dependent body then composition/application projection | inner `NatTrans.app`, equivalence and projection chains | outer major argument 6 alignment: 95.869 s -> below resolution; restoration 93.567 s | producer S; gateway S; amplifier S/P; boundary S |

Historical S2/pre-finalization provenance remains U; the current import pin does not reconstruct it. The shared tool selects costly exact pairs but does not tag every M1 call with a unique source declaration and structure field. That additional per-call field/declaration tag, joined to the historical S2 tree, is needed to divide projection direct time among individual named accessors without double-counting.

## Audit note

The nested `.app` producer, dependent gateway, and projection path are **S** with **P** field ownership. Outer-major-premise alignment/restoration change M0; they demonstrate an API boundary, not a descendant-only cut.
