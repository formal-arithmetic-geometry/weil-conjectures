# Mismatch-to-definition attribution: ImageHomCounit

## A. Root and source boundary

The pinned `probes/mprwe/Original.lean` (SHA-256 `df4aa7742e3aa3d356b640a63fc8668ec0cae3e4e9455ce242ce9538997017f3`) checks the final `exact h` in `imageHomIso_counit`. Lean 4.35.0 and the pinned current import tree are specified by the shared MDA contract. The saved S2 snapshot in `ccmoa/s2-snapshot.txt` gives the exact `Eq.{u+2}` actual/expected Expr trees (hashes 349589718/1301129340). Its first unequal type/data child is raw `DerivedCategory (Sheaf T.left.Etale (ModuleCat A))` on the inferred side versus `DerivedCategoryModule A T.left` on the declared side. Implicit category and derived-category instances are retained in that snapshot. `DerivedCategoryModule` is an `abbrev`; `DerivedCategory` is a regular definition with height 15. The target theorem is opaque.

Fresh MDA root `2129` succeeds: 6,359,958 calls, 117,357.356 ms comparison-exclusive, 4,781,271 M1 calls/113,061.350 ms M1 exclusive, 276 M2 calls/3,956.823 ms, 1,578,409 Matched calls/115.828 ms, and one Unclassified call/82.021 ms. M1 median/max depth is 162/204; M1 mean fan-out is 1.330. These trace times include high Expr-serialization overhead; use paired prior counters for intervention effects. `mda/summary.jsonl.gz` and `mda/groups.jsonl.gz` reconcile every call and direct time.

## B. Gateway-to-cost (§4.1)

Each exact child pair is in the named `mda/pair-<call>.json.gz`; the displayed head is only a locator. Subtree times below are **inclusive all-label** times and overlap. The final column is the additive **direct M1** group total for that branch/component over the root, not an extra charge to the selected node.

| Gateway ID | Parent M0 path | Kernel branch / exact child pair | Source/API candidate | Subtree M1 calls | Inclusive subtree ms | Direct M1 ms, branch/component | Evidence |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| 2129:2 | root | `quick/dependent-body[6]`; `Eq` / `Eq` | final dependent equality | 4,781,271 | 117,216.023 | see group rows | S |
| 2129:213 | `binder_body[6]` | `application/argument[1]`; `CategoryStruct.comp` / same | composition side of raw/wrapper equality | 4,780,608 | 117,069.937 | application argument[1]: 4,590.544 | S |
| 2129:214 | call 213 | `second_whnf`; `DFunLike.coe` / same, **M2 entry** | equivalence coercion exposure | 4,780,607 | 116,725.626 | second_whnf: 54,131.260 | S |
| 2129:223 | call 222 | `second_whnf`; localization category `_aux_5` / same | category instance path | 4,780,600 | 115,582.003 | second_whnf as above | S |
| 2129:260 | call 223 | `lazy_delta/argument[6]`; `DFunLike.coe` / same | nested equivalence major premise | 4,780,575 | 115,173.961 | lazy_delta argument[6]: 1,591.992 | S |

The first large selected M1 child is call 213. Call 214 is M2, then call 215 returns to M1; a large inclusive subtree at an M2 node does not make all descendants M2. The mapped accessor fields are `CategoryStruct.comp` index 2 and `Functor.map` index 1. The projection group contributes 1,253,595 M1 calls and 19,616.924 ms direct M1 time, but its individual downstream field shares are unavailable: costly ancestor chains occupy the top-node selection. The aggregate source tag is `unknown`, so source ownership comes from the S2 join and the original probe, not from a claimed Kernel source declaration.

## C. Definition/API path (§4.2) and causal chain (§4.3)

| Candidate | Role | First seen | Kernel path and cost | Intervention | Evidence |
| --- | --- | --- | --- | --- | --- |
| Raw `DerivedCategory` vs `DerivedCategoryModule` | producer | S0/S2 | first unequal `Quiver.Hom` endpoint in S2; whole root 4,781,271 M1 calls | full inferred-type alignment | S |
| Dependent equality body and `CategoryStruct.comp` | gateway | calls 2/213 | 4,780,608 M1 descendants; 117,069.937 ms inclusive all-label | broad alignment removes this obligation | S |
| `DFunLike.coe`, `EquivLike.coe`, `Equiv.toFun` | gateway/path nodes | calls 214-216 | `second_whnf` M1 group 54,131.260 ms direct; call 214 itself M2 | none isolated | S/P |
| Localization category `_aux_5`, `Functor.map`, `equivShrink` | downstream amplifiers | calls 223 onward | repeated projection and application paths; projection M1 group 19,616.924 ms direct | none isolated | P |

Source raw endpoint / declared wrapper endpoint -> S2 unequal dependent `Quiver.Hom` type -> root M0 -> dependent body call 2 -> application argument call 213 -> WHNF/equivalence and localization category paths -> 4,781,271 M1 descendants and 113,061.350 ms M1 exclusive -> full inferred-type alignment removes the root. The link from the exact Kernel pair to the authored source is the saved S2 Expr join; assigning individual downstream definition shares remains inferred because the additive source tag is `unknown`.

## D. Intervention and E. boundary

The type-correct full inferred-type alignment keeps `h` and the final consumer but copies the complete inferred equality: 6,359,958 calls become 2,881 calls (largest recorded root), while multiple dependent arguments change. It is an API-level counterfactual, **not** an M0-preserving one-factor cut. Expanding only the outer wrapper is a narrower negative control and increases the workload to 9,539,325 calls. Source spelling controls leave the elaborated pair unchanged and remain slow. The cheap boundary is the aligned whole equality; restoring the direct raw/wrapper target punctures it. Status: fragile but effective. A type-correct control changing only the first S2 endpoint while retaining all dependent arguments is still missing.

## Summary row (§4.4)

| Case | Producer | Gateway | Amplifier | Best one-factor test/effect | Levels |
| --- | --- | --- | --- | --- | --- |
| ImageHomCounit | raw/wrapper derived-category endpoint | dependent `Eq` body -> composition argument -> coercion/WHNF | localization category, equivalence and projection chains | wrapper-only expansion: 6,359,958 -> 9,539,325 calls (negative); no successful one-factor cut | producer S; gateway S; amplifier P; boundary S |

Historical S2 is available; pre-finalization S3 is not. The current trace cannot assign non-overlapping M1 exclusive time to each named definition after a shared gateway. That would require a declaration/field tag on **every** M1 call (the current tool emits exact Expr/field detail only for selected top nodes), joined to the S2 tree, while preserving the additive direct-cost partition.

## Audit note

Raw/wrapper endpoint divergence is **S**: the exact child and broad alignment
are present, but the alignment changes multiple obligations. The wrapper-only
negative control confirms that spelling/expansion is not sufficient. Gateway is
**S** for path evidence and amplifier ownership **P**; no D causal cut is
claimed.
