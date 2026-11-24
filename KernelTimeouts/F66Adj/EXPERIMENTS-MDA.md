# MDA attribution: F66Adj

## Scope and evidence

The source declaration is `imageHomIso_naturality` at revision `f66ad18a9ed8931b2d386105528c40a56fae8e0c`; the measurement import tree is `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`, Lean 4.35.0. The exact root is the proposition-type conversion for argument 39 (`hR`) of `homIso_naturality_of_counit`, after its first 38 dependent arguments are instantiated. `probes/mprwe/Original.lean` and `EXPERIMENTS-MOE.md` provide source/local-context evidence; `mda/base.jsonl.gz` and `mda/top-*.jsonl.gz` contain the new kernel trace (root 6122). The `source=unknown` key in the group output means the configured namespace prefix did not occur as a nearest parent-call head; it is not evidence that source attribution is unknown after the MOE join.

The source gives `imageRestriction_counit A _ _ (Over.mk f.left)` while the helper expects the direct restriction-counit proposition at local scheme `X`. S2 shows the material leaf `Over.left (Over.mk f.left)` versus `X` inside `DerivedCategoryModule`, under `Eq` and `Quiver.Hom`. The proof-term snapshot diverges at `root/arg/arg` (`app` versus `fvar`). The MDA root succeeds with 3,897,905 calls, 2,961,163 M1, 9 M2, 936,732 Matched, and 45,914.132 ms comparison-exclusive. Its M1 direct time is 45,808.123 ms; instrumentation overhead makes this time incomparable to READY4.2 baseline time, while counts and same-trace partitions remain comparable.

## 4.1 Gateway-to-cost

These are nested inclusive subtrees. Call 60 owns the first large child; later rows describe its path and must not be added.

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | Subtree calls / M1 calls | Subtree comparison-exclusive | Evidence |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| 6122:60 (parent 1) | `root/argument[1]` | application argument 1 | `CategoryStruct.comp` / `CategoryStruct.comp` | `hR` equality composition side | 3,897,751 / 2,961,059 | 45,841.213 ms | S: exact Expr pair and S2 join |
| 6122:61 (parent 60) | `.../whnf` | `second_whnf` | `EquivLike.coe` / `EquivLike.coe` | equivalence coercion | 3,897,750 / 2,961,058 | 45,373.821 ms | S: downstream path |
| 6122:68 (parent 62) | `.../argument[0]` | application argument 0 | `CategoryStruct.comp` / `CategoryStruct.comp` | nested composition | 3,897,743 / 2,961,052 | 44,504.093 ms | S: downstream path |
| 6122:69 (parent 68) | `.../argument[7]` | `lazy_delta` argument 7 | `DFunLike.coe` / `DFunLike.coe` | nested equivalence/coercion | 3,897,669 / 2,961,004 | 44,330.332 ms | S: downstream path |
| 6122:461404 (parent 72) | `.../argument[0]` | application argument 0 | `NatTrans.app` / `NatTrans.app` | natural-transformation component | 3,436,334 / 2,610,465 | 36,113.998 ms | S: downstream path, not separate owner |

The exact full Exprs are in `mda/top-01.jsonl.gz`; selected deeper nodes continue in `top-02` through `top-05`. The first expensive branch is the equality's composition argument at call 60. `Over.left` is present on both sides of the exact root/child Exprs, but the selected trace does not assign an isolated exclusive share to its reduction or prove it was the first unfolded head.

## 4.2 Definition/API path

Direct group rows below are disjoint within this trace. The nested call-60 and call-461404 times above are inclusive and are shown only once as gateway/path evidence.

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| specialized `imageRestriction_counit ... (Over.mk f.left)` vs helper's direct proposition | producer | S0/S2 | root proposition, scheme leaf | 2,961,163 root total | 45,808.123 ms root M1 direct total | direct `restriction_counit` | D |
| `CategoryStruct.comp` equality argument | gateway | call 60 | `application/argument[1]` | 2,961,059 inclusive | 45,841.213 ms inclusive | direct proposition changes M0 | S |
| `EquivLike.coe` / `Equiv.toFun` / `Equiv.invFun` | amplifier path | calls 61-72 | `second_whnf` | 310,390 direct | 15,642.337 ms direct | no local field control | S path; P field share |
| category/equivalence projection field 0 | amplifier component | aggregate | projection | 761,198 direct | 11,194.275 ms direct | no local field control | P field identity |
| application argument 1 | dependent amplifier | aggregate | application | 438,420 direct | 3,895.205 ms direct | no local control | P |
| application argument 0 | dependent amplifier | aggregate | application | 719,539 direct | 2,893.311 ms direct | no local control | P |
| `NatTrans.app` | amplifier path | call 461404 | application argument 0 | 2,610,465 inclusive | 36,113.998 ms inclusive | no local control | S path; overlapping with call 60 |
| proof proposition types | amplifier component | aggregate | proof irrelevance | 73,771 direct | 1,331.771 ms direct | no local control | P |

`DerivedCategoryModule`, `Scheme.instCategory`, `instCategoryOver`, `catToReflQuiver`, `DFunLike.coe`, and linear-map projections are present in the MOE/M1P source-to-kernel path. The new selected trace directly confirms the composition/equivalence/`NatTrans.app` segment, but does not isolate a non-overlapping share for each scheme or instance field. A deeper selected-node trace with source inheritance through all namespaces and generated maps for these structures would be needed for that finer allocation.

## 4.3 Root-to-source chain

Source `imageRestriction_counit A _ _ (Over.mk f.left)` -> supplied proposition contains `Over.left (Over.mk f.left)` while instantiated helper argument 39 contains local `X` (S2 M0) -> kernel `Eq`/`Eq` root 6122:1 -> composition argument at call 60 -> `EquivLike.coe`, `Equiv.toFun`, nested `CategoryStruct.comp`, `DFunLike.coe` -> `NatTrans.app` at call 461404 -> 2,961,059 M1 calls and 45,841.213 ms inclusive under call 60. The source/API producer and one-factor direct-counit intervention are D. The exact gateway/path are S. Scheme/instance field allocation remains P.

## 4.4 Summary

| Case | Producer | Expansion gateway | Cost amplifier | Best intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| F66Adj | specialized over-object counit vs helper's instantiated direct proposition (D) | `Eq` composition argument, call 60 (S) | equivalence coercion and composition path into `NatTrans.app`, with dependent scheme/instance fields (S path; P individual fields) | direct `restriction_counit` at argument 39: 3,897,905 -> 2,881 captured calls; restored specialized proof -> 3,897,905 | D API counterfactual; M0 changes |

The direct-counit control keeps the helper, preceding 38 arguments, and theorem obligation. It changes the proposition representation at argument 39, so it is not an M0-preserving descendant cut. A preceding-`τq` edit leaves the slow pair and about 3.90M calls. The currently cheap direct proposition boundary is fragile: restoring `imageRestriction_counit ... (Over.mk f.left)` punctures it; full replay wall time changes from 3.30 s to 34.42 s. Exact cost relocation in the fast variant is unavailable because its threshold-zero largest root is a different conversion (2,881 calls), not a matched MDA subtree.

## Audit note

The specialized-counit producer and restored fast/slow pair are **D** as an
API counterfactual. The composition gateway is **S** from the exact parent and
child expressions. Equivalence, scheme, and instance field ownership stays
**P** because the only successful control changes M0 and has no paired subtree.
