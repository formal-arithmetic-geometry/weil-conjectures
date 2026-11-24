# Mismatch-to-definition attribution: PR1563

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); historical probe snapshot `1ef1fddac73`. The fresh MDA run used `probes/mprwe/OriginalComposition.lean` (SHA-256 `7193bfe627ae36c05f17aebe8cdb7fd2424b6f9a467bbe9aca13c4d83b277a09`) in the pinned current import tree. The selected comparison is root 12122 in this run, not the READY4.2 serial 7269. Its exact pair and universes are in `mda/selected-root.jsonl.gz` (`mda_top`, call 1).

## A. Root and first divergence

The compared values have the shared `CategoryStruct.comp` head. The original `Eq.mpr` argument-3 dependent domain compares two `Eq` propositions whose carrier and left equality side are structurally identical; the right side is the concrete composition pair. The old S5 audit found an `fvar` versus an application at `root/arg/arg` in the `Eq.mpr` result. Historical S2 and pre-finalization values are unavailable, so the earliest verified exact divergence is S5. `Eq.mpr` has hint `regular:1`; `CategoryStruct.comp` is an `abbrev` exposing `CategoryStruct` projection 2. The full root succeeds with 2,575,237 calls, 23,716.772 ms comparison-exclusive and 14,231.671 ms reduction time. Labels: M1 1,929,717 calls / 23,176.531 ms; M2 979 / 374.706 ms; Matched 644,533 / 59.525 ms; Unclassified 7 / 0.146 ms. M1 depth reaches 97; mean fan-out is 1.334 and maximum 21.

## B. Gateway-to-cost (§4.1)

Exact structural expressions, implicit arguments and universes are keyed by `(root, call)` in the compressed JSONL. Subtree times below include all labels and are inclusive; rows 3 and 1159782 are disjoint siblings, while their descendants overlap them. The shared tool does not export M1-only exclusive time for selected subtrees, so that column is explicitly unavailable.

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Total subtree exclusive time | Evidence |
| --- | --- | --- | --- | --- | ---: | --- | ---: | --- |
| 12122:2 | root 12122:1 | `second_whnf` / exposure | `FullSubcategory.category._aux_5` / same head | concrete category behind `CategoryStruct.comp` | 1,929,717 | unavailable by subtree | 23,610.907 ms | S: exact pair and cost, source join provisional |
| 12122:3 | `root/whnf` | `lazy_delta` / argument 7 | `CategoryStruct.comp` / `CategoryStruct.comp` | nested concrete composition | 863,764 | unavailable by subtree | 10,479.483 ms | S: exact child, disjoint branch |
| 12122:1159782 | `root/whnf` | `lazy_delta` / argument 6 | `NatTrans.app` / `NatTrans.app` | natural transformation component | 852,876 | unavailable by subtree | 10,460.981 ms | S: exact child, disjoint branch; child is M2 |
| 12122:1159784 | argument 6 via `Iso.inv` | projection / projection 0 | exact lambda pair in JSONL | derived inverse component | 852,875 | unavailable by subtree | 10,220.845 ms | P: nested in prior row; field owner unresolved |

The first costly *child* is 12122:2, whereas `CategoryStruct.comp` 12122:3 is the first selected composition branch. The `NatTrans.app` sibling is M2 at entry and later contains M1; it must not be counted as an M1 child. No additive sum of the four inclusive rows is valid.

## C. Definition/API path (§4.2)

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive time | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| Concrete `Eq.mpr`/composition proof | producer candidate | S0 source, exact pair S5 | root `CategoryStruct.comp` | 1,929,717 root total | 23,176.531 ms root total | generic pullback helper | P: broad source change |
| `FullSubcategory.category._aux_5` | first observed gateway | 12122:2 | `second_whnf` | 1,929,717 subtree | unavailable by subtree | no local control | S for traversal; P for causal ownership |
| `CategoryStruct.comp` | composition gateway/path | 12122:3 | `lazy_delta` argument 7 | 863,764 subtree | unavailable by subtree | no typed major-premise alignment | S for traversal |
| `NatTrans.app` -> `Iso.inv` -> projection 0 | downstream amplifier path | 12122:1159782 | `lazy_delta`, WHNF, projection | 852,876 subtree | unavailable by subtree | no local control | S for path, P for field identity |
| Projection component 0, all direct M1 calls | amplifier component | aggregate | projection | 503,729 | 8,527.365 ms | no local control | S for partition, P for source owner |
| WHNF-exposure component, all direct M1 calls | gateway component | aggregate | `second_whnf` | 205,160 | 3,621.844 ms | no local control | S for partition |

The last two rows are additive direct-cost groups over the full root, not costs assigned to any one selected inclusive subtree. The source key in these groups is `unknown`; the Kernel Expr path alone cannot prove which user declaration owns a descendant. The selected exact pairs nevertheless expose `CategoryStruct.comp`, `NatTrans.app`, `Iso.inv`, and projection traversal. The field map identifies `CategoryStruct.comp` as field 2; projection 0 at call 1159784 has no resolved structure owner and is left unnamed.

## D. Root-to-source chain (§4.3)

Concrete `Eq.mpr` proof construction and derived functor composition (source, P) -> `Eq` right side represented by two concrete `CategoryStruct.comp` applications (S5, S) -> M0 at root 12122:1 -> `second_whnf` exposes `FullSubcategory.category._aux_5` at 12122:2 (S) -> disjoint argument-7 composition and argument-6 natural-transformation subtrees (S) -> projection/WHNF/application descendants (S) -> 23,176.531 ms root M1 direct-exclusive time (D measurement) -> named generic pullback helper avoids the old target check (S API-level counterfactual).

The older `Before.lean`/`After.lean` same-statement control changes the source proof from concrete simp expansion to `higherDirectImageRawOverPullback_eq_moduleFactors`, backed by `rawTriangleMap_whiskerLeft_eq_comp`. It changes more than one Kernel obligation. Target checking fell from 68.2 s to 15.2 s, while the helper retained a 32.4-32.7 s floor. The prior provider-alignment diagnostic changed the dependent root and is not an M0-preserving control. Restoring the concrete proof restores the slow target. No new one-factor typed child intervention is established by this run.

## E. Summary (§4.4)

| Case | Mismatch producer | Expansion gateway | Cost amplifier | Boundary and effect | Overall evidence |
| --- | --- | --- | --- | --- | --- |
| PR1563 | concrete `Eq.mpr`/composition versus generic helper (P) | `second_whnf` exposure of `FullSubcategory.category._aux_5` (S observed, P causal) | nested `CategoryStruct.comp` and `NatTrans.app`/`Iso.inv` projection paths (S traversal, P ownership) | generic helper: target 68.2 -> 15.2 s; API-level, broad | P for source cause; S for measured path |

The helper boundary is fragile but effective: reintroducing the concrete composition proof punctures it. The remaining 15.2 s target and 32.4-32.7 s helper costs are separate obligations, not removed subtree time. A stronger causal test needs a type-correct major-premise alignment at 12122:3 under the original `Eq.mpr` telescope. The MDA extension also needs per-label exclusive nanoseconds accumulated at each selected subtree and a source-declaration context tag to measure M1-only branch costs and source ownership directly. Historical S2 provenance remains U.

Artifacts: `mda/selected-root.jsonl.gz` (exact pairs and complete aggregate partition), `mda/analysis.txt`, and `mda/fields.map`. The fresh root's label, transition and direct-group totals all reconcile.

## Audit note

The source producer remains **P**: historical S2 is missing and the helper changes multiple obligations. `FullSubcategory.category._aux_5` and composition are **S** as measured traversal, but have no local one-factor causal cut.
