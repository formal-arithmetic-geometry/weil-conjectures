# Mismatch-to-definition attribution: NativePullTensor

Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; original case probe snapshot `1ef1fddac73ed8d77efa0edd9db659d19ef99cb3`; measurement import revision `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`. Probe: `probes/mprwe/OriginalRoot.lean` (SHA-256 `fd0375c5523f948e280c0537a7c6cc4b3fde533dd920f233217ad92e5b278976`). Root `18506` is the original dependent comparison reached while checking `AlgebraicGeometry.ProEtaleWeilSheaf.nativePullTotalTensor`, under the 12 original binders and the `@Exists.choose` predicate/proof application domains. Its exact structural Expr pair, including universes and implicit arguments, is `mda/selected.jsonl.gz`, call 1; the local context and source site are in `probes/ValuePrefixes.lean`, `probes/HeadAudit.lean`, and `EXPERIMENTS-CCMOA.md`.

The fresh field-aware root summary records 2,685,580 calls, 49,566.395 ms comparison-exclusive and 12,889.180 ms reduction-exclusive time, maximum depth 81, and a successful DefEq result. The complete `mda_group` rows sum independently to 2,685,580 calls and 49,566.394628 ms; their M1 columns sum to 1,120,689 calls and 48,802.270327 ms (98.46% of this trace's comparison-exclusive time). The previous complete READY4.2 root had the same call/label counts: M0 1, M1 1,120,689, M2 12,041, Matched 1,552,849; its M1 median depth was 44 and maximum fan-out 28. M2 and Matched **times in this fresh trace are U** because the process was stopped before the JSONL coverage/aggregate footer; the MDA rows and stderr root summary were already complete. Earlier M1P M2/Matched timings are separate runs and are not added to this trace. The trace overhead is substantial; these are attribution timings, not release-performance timings.

## 4.1 Gateway-to-cost

| Gateway ID | Parent M0 path | Kernel branch and exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- |
| `18506:2` | `root/binder_domain[0]` | `quick/binder-domain[0]`; exact `CategoryTheory.Iso`/`CategoryTheory.Iso` Expr pair in `mda/selected.jsonl.gz` | Instantiated `Exists.choose` predicate domain | 1,120,689 in its subtree | 48,802.270 ms in its subtree | S for original dependent-root entry |
| `18506:65` | call 2 | `application/argument[2]`; exact `Functor.comp`/`Functor.comp` pair | Source `Iso` endpoint | 560,330 in its subtree | Not exported per inclusive subtree | S path, U isolated M1 time |
| `18506:86` | call 65, endpoint argument 6 | `lazy_delta/argument[6]`; exact `Functor.obj`/`Functor.obj` pair; exposed `Functor.mk`/`Functor.mk` | Hidden `Functor.uncurry` major premise through `Functor.obj` | 560,322 in its subtree | Not exported per inclusive subtree | S gateway path |
| `18506:95-98` | `Functor.mk` object component | `quick/dependent-body[1]` `Functor.obj` pair -> `second_whnf` `HomologicalComplex.mapBifunctor` pair -> `lazy_delta/argument[12]` `_proof_10` pair -> `proof_irrelevance/proposition-type` exact `forall` pair | Total tensor functor and dependent proof proposition | 50,949 at call 95; 25,492 at call 98 | Not exported per inclusive subtree; call 98 all-label inclusive 21,085.921 ms | S path, P as unique cost owner |

Selected inclusive rows overlap. Call 2 contains all M1 cost and receives it once. The non-overlapping direct M1 partition in `mda/selected.jsonl.gz` gives the following largest gateway/component groups; `source` is the nearest head, not a causal proof about that declaration:

| Gateway/component/source path | M1 calls | Direct M1 exclusive ms |
| --- | ---: | ---: |
| `second_whnf/whnf-iota-exposure` / `nativeTensorTotal._proof_10` | 8,932 | 8,775.106 |
| `lazy_delta/argument[7]` / `nativeTensorTotal._proof_10` | 5,236 | 7,337.005 |
| `application/function-head` / `tensor_map_comm` | 58,036 | 4,995.674 |
| `application/function-head` / unknown nearest source | 17,336 | 1,837.575 |
| `lazy_delta/argument[6]` / `nativeTensorTotal._proof_10` | 2,530 | 1,634.652 |
| `application/function-head` / `nativeTensorTotal._proof_10` | 17,336 | 1,544.482 |
| `projection/projection[0]` / `tensor_map_comm` | 29,480 | 1,025.907 |

These rows are direct costs at distinct `(branch, nearest source, component)` keys and can be added. The top-pair selector follows one expensive spine; it does not retain an exact pair for every high-cost aggregate group. Resolving those pairs needs bounded group representatives or a full ancestor-path key. `projection[0]` is a recorded index; the field map does not establish the major premise for that aggregate group.

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen | Kernel path | M1 calls / exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| Two concrete `Functor.uncurry` major premises, one involving the stored `(exists_nativePullTotalTensor ...).choose` route | Mismatch producer representation | S2/stored Expr; exact pair in call 1 and the endpoint probes | `Iso` source/target endpoint, `Functor.obj` argument 4 | Full-root share not separately isolated | Endpoint-only major-premise alignment | S for divergence; P for original source choice |
| Instantiated `Exists.choose` predicate/proof domains | Expansion boundary | call 1 -> call 2 | `quick/binder-domain`; source prefix probe independently measures both domains | 1,120,689 / 48,802.270 in call-2 subtree | No type-correct full-root alignment | S |
| `Functor.comp` then `Functor.obj` (`abbrev`, body projects `Functor.obj` field 0) | Expansion gateway within domain | calls 65 and 86 | application argument -> lazy delta -> `Functor.mk` | 560,322 M1 calls in call-86 subtree; M1 time not isolated | One-factor endpoint alignment 11.396/11.355 s -> 0 ms | S gateway; D extracted endpoint only |
| `HomologicalComplex.mapBifunctor` and `nativeTensorTotal._proof_10` proposition | Cost amplifier path | calls 95-98 | dependent body, WHNF, lazy delta, proof irrelevance | Direct `_proof_10` WHNF 8,775.106 ms and argument[7] 7,337.005 ms | No same-root cut | S path/direct cost; P causal isolation |
| `tensor_map_comm`, `Functor.map`, `NatTrans.app`, category composition | Downstream amplifier path | direct MDA groups; old reduction counters | application function-head/argument and projection | Function-head group 58,036 / 4,995.674 | No same-root cut | S direct group; P particular field cause |

The proof proposition is a data-bearing dependent type: call 98 compares an exact `forall` pair after proof irrelevance enters the proposition types. The two source/target endpoints repeat similar object-provider paths, but the root-level selected subtree is not a separate measurement of each endpoint. The original S2 source writes the same outer `Exists.choose`, `Functor.comp`, and `Functor.obj` vocabulary; the hidden provider terms differ after elaboration. Their selection mechanism was not isolated by an alternate-provider frozen replay.

## 4.3 Root-to-source chain

Original `nativePullTotalTensor` construction and stored `(exists_nativePullTotalTensor ...).choose` provider -> distinct concrete functor major premises inside equal-headed `Functor.obj` applications (exact endpoint pair in call 86 and the earlier `HeadAudit`/`MajorAlignment` probes) -> original `@Exists.choose` dependent-domain M0 at call 1 -> call 2 `Iso` binder domain -> call 65 `Functor.comp` endpoint -> call 86 `Functor.obj` lazy-delta gateway and `Functor.mk` exposure -> call 95 `HomologicalComplex.mapBifunctor` -> call 97 `_proof_10` and call 98 proposition type -> 1,120,689 M1 calls / 48,802.270 ms, with the direct WHNF, lazy-delta, function-head, and projection rows above -> endpoint-only one-factor major-premise alignment makes the extracted object pairs immediate. The last control is **not** evidence that the original dependent root is fixed.

## 4.4 Summary and boundary

| Mismatch producer | Expansion gateway | Cost amplifier | Best one-factor intervention and effect | Evidence |
| --- | --- | --- | --- | --- |
| Hidden concrete `Functor.uncurry`/`Functor.obj` provider pair in the `Exists.choose` domains | Dependent `Iso` binder domain, then `Functor.obj` lazy delta to `Functor.mk` | `mapBifunctor`, `_proof_10` proposition types, `tensor_map_comm` function heads and projection paths | Replace only the right `Functor.obj` major premise in the extracted endpoint: 11.396/11.355 s -> 0/0 ms; reverse comparison restores 11.284/11.301 s. Full-root effect U. | Producer S as representation, P as source selection; gateway S; amplifier S for path/direct cost, P for unique cause; intervention D at endpoint, U at root |

The endpoint replacement is type-correct and preserves that endpoint's result type, but the old `InvalidRootAlignment.lean` attempt changes the dependent telescope's required type and does not constitute a valid original-root intervention. The same-body regular/abbrev control (regular/regular 0 ms; abbrev/abbrev 11.251 s) is a valid endpoint boundary test, not a full-root repair. `Functor.obj` is an `abbrev` exposing projection field 0; sharing its major premise makes the endpoint cheap, while separately constructed premises puncture the boundary. The `Exists.choose` domains remain fragile because the preceding provider determines their dependent types. Restoring an endpoint provider restores endpoint cost; no root-level puncture result is claimed.

Remaining uncertainty: the exact source decision selecting the two hidden providers, separate M1 exclusive time for each `Exists.choose` domain and each endpoint, M2/Matched time in the fresh partial JSONL, and an original-root-valid one-factor provider/domain alignment. The MDA writer emitted all groups and top pairs but the full probe continued to high memory use; stopping it left an incomplete JSONL footer. A bounded trace that flushes coverage immediately after the selected root, plus path-preserving group ancestry and a type-correct full-telescope replay, is needed for those measurements. No finalization cause is inferred from the imported declaration.
## Audit note

The endpoint replacement is **D** for the extracted endpoint obligation, but
its effect on the original dependent root is **U**. The hidden provider source
selection is **P**, not D. `Exists.choose`, `Functor.obj`, and `mapBifunctor`
are **S** path evidence; separate provider/domain shares remain **U**.
