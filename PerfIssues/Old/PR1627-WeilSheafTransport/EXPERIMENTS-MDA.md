# Mismatch-to-definition attribution: PR1627

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); historical probe snapshot `1ef1fddac73`. Three fresh MDA traces used `probes/mprwe/OriginalGeneratedFields.lean` (SHA-256 `7bb22081d9502b381c79089785561fac91321cf4605504799615c9ab483e856a`) in the pinned import tree. Each selected root was independently validated against complete aggregate, transition and direct-group totals. Exact structural pairs, including implicit arguments and universes, are in `mda/root-*.jsonl.gz`.

## A. Generated obligations and M0

The original source constructs `powFunctor` directly with `IsoAlgebra.mk` for objects and `ObjectProperty.homMk` for maps. Declaration processing stores three opaque law constants `_proof_1`, `_proof_2`, `_proof_3`. A prior exact stored-value audit locates `_proof_2`'s first unequal node at `root/body/arg/fn/fn/fn`: `ObjectProperty.homMk` with explicit `Algebra.instCategory` and `Algebra.IsIsoStr` arguments versus `CategoryStruct.id`. `_proof_3`'s corresponding checked argument was structurally aligned. The exact pre-finalization generated law Expr was not captured; finalization causality is U. Hints: `powFunctor` regular:59, `frobeniusPowPullback` abbrev, `CategoryStruct.id` abbrev, `liftOfStr` regular:6, generated laws opaque.

The new root 15228 is a dependent proposition comparison with `ObjectProperty.homMk` / `CategoryStruct.comp` at call 6. Roots 11094 and 11621 are distinct `Quiver.Hom` comparisons that expose `WeilSheaf.frobeniusPullback` / `ProEtaleWeilSheaf.frobeniusPowPullback` at calls 21. The probe also checks generated `_proof_1` and `_proof_2` `id` argument-1 domains separately: 10.210 s and 44.155 s in the counters discovery pass. The MDA patch records root serials but not the calling declaration/field; therefore it cannot prove a one-to-one root-to-`_proof_1`/`_proof_2`/`_proof_3` map. In particular the three selected roots must not be added as three independent field costs. A declaration/field context tag at `Kernel.check` and `isDefEq` entry would be required to finish that mapping.

| Selected root | Calls | M1 calls / exclusive ms | M2 calls / exclusive ms | Matched calls / exclusive ms | Max depth | Exact first selected path |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 11094 | 2,627,564 | 632,685 / 6,032.385 | 364,191 / 3,322.530 | 1,630,687 / 603.459 | 55 | `Quiver.Hom` -> `Mod.Hom` -> `Endofunctor.Algebra.a` |
| 11621 | 4,696,766 | 1,129,351 / 11,738.771 | 651,302 / 6,172.834 | 2,916,112 / 1,145.390 | 55 | `Quiver.Hom` -> `Mod.Hom` -> two `Endofunctor.Algebra.a` arguments |
| 15228 | 10,904,899 | 2,619,482 / 23,288.322 | 1,512,663 / 12,479.586 | 6,772,753 / 2,528.957 | 61 | dependent `Eq` -> `homMk` / `CategoryStruct.comp` |

The largest root has 38,353.313 ms comparison-exclusive and 18,120.527 ms reduction time. Matched is 6.773M calls and 2.529 s, a material 6.6% of its comparison-exclusive time; it is separate from M1 and M2. Roots 11094 and 11621 have 9,964.110 and 19,062.697 ms total comparison-exclusive respectively. These are separate replay comparisons, not additive portions of root 15228.

## B. Gateway-to-cost (§4.1)

Selected subtree exclusive times include all labels; M1-only subtree exclusive time is not exported. Rows nested under another row are path evidence, not extra cost ownership. All exact child Exprs are keyed by root/call in the corresponding compressed JSONL.

| Gateway ID | Parent M0 path | Kernel branch | Exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Total subtree exclusive time | Evidence |
| --- | --- | --- | --- | --- | ---: | --- | ---: | --- |
| 11094:2 | root 11094:1 | `second_whnf` | `Mod.Hom` / `Mod.Hom` | generated-law Hom domain | 632,685 | unavailable by subtree | 9,958.373 ms | S: exact child/cost |
| 11094:21 | via `Algebra.a`, projection, structure field | application / argument 2 | `WeilSheaf.frobeniusPullback` / `ProEtaleWeilSheaf.frobeniusPowPullback` | concrete functor representation | 384,348 | unavailable by subtree | 5,987.100 ms | S: exact divergent child |
| 11621:2 | root 11621:1 | `second_whnf` | `Mod.Hom` / `Mod.Hom` | generated-law Hom domain | 1,129,351 | unavailable by subtree | 19,056.995 ms | S: exact child/cost |
| 11621:12 | root/whnf | application / argument 8 | `Endofunctor.Algebra.a` / same | first algebra component | 632,683 | unavailable by subtree | 10,539.094 ms | S: disjoint from argument 9 |
| 11621:2627564 | root/whnf | application / argument 9 | `Endofunctor.Algebra.a` / same | second algebra component | 496,667 | unavailable by subtree | 8,511.990 ms | S: disjoint sibling |
| 15228:2 | root 15228:1 | quick / dependent body 2 | `Eq` / `Eq` | generated proof proposition | 2,619,482 | unavailable by subtree | 38,296.865 ms | S: first expensive child |
| 15228:6 | dependent body 2 | application / argument 2 | `ObjectProperty.homMk` / `CategoryStruct.comp` | direct generated-field API | 2,619,481 | unavailable by subtree | 38,244.037 ms | S: exact divergent child |
| 15228:23 | via `Algebra.Hom.mk`/`Hom.f` | `second_whnf` | `CategoryStruct.comp` / `Mod.comp` | concrete composition gateway | 2,619,349 | unavailable by subtree | 38,064.397 ms | S: M1 descendant; prior nodes include M2 |
| 15228:24 | 15228:23 | `lazy_delta` / argument 12 | `Algebra.Hom.f` / same | induced Hom projection | 632,683 | unavailable by subtree | 10,044.367 ms | S: one of several nested branches |
| 15228:25 | 15228:24 | projection / index 0 | `InducedCategory.Hom.proj` / same | concrete projection path | 632,683 | unavailable by subtree | 10,035.206 ms | S: owner field name unresolved |

`InducedCategory.Hom` projection 0 is unresolved by the supplied field map and is recorded as `field:0`, not assigned an invented field name. At 15228:15 and 15228:22 the entering label is M2, then 15228:23 returns to M1; the descendant tree is mixed. The 11094:21 and 11621:21 paths show the concrete pullback pair under different surrounding obligations.

## C. Definition/API path (§4.2)

| Candidate definition/API | Role | First seen | Kernel path | M1 calls | M1 exclusive time | Intervention | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- | --- |
| Direct `IsoAlgebra.mk` / `ObjectProperty.homMk` | producer | S0 source, exact stored pair S4 | 15228:6 and generated laws | 2,619,481 in selected subtree | unavailable by subtree | `liftOfStr` | S: API-level control, caller mapping U |
| Dependent proof proposition | gateway | 15228:2 | quick dependent body -> application | 2,619,482 | unavailable by subtree | generic helper removes direct laws | S |
| `Endofunctor.Algebra.Hom` and `CategoryStruct.comp` / `Mod.comp` | downstream gateway and amplifier | 15228:14-23 | WHNF, application, lazy delta | 2,619,349 at 15228:23 | unavailable by subtree | no local typed control | S traversal, P causal ownership |
| `Endofunctor.Algebra.a`, `FullSubcategory.proj` | amplifier path | 11094:12-13; 11621:12-13 | application, projection | 632,683 in each selected branch | unavailable by subtree | no local control | S traversal |
| `frobeniusPowPullback` / dependent body 2 | direct M1 source-context group | 15228 aggregate | quick | 221,952 | 4,621.077 ms | generic helper broad | S partition, P ownership |
| `frobeniusPowPullback` / application argument 3 | direct M1 source-context group | 15228 aggregate | application | 444,031 | 4,359.971 ms | generic helper broad | S partition, P ownership |
| `frobeniusPowPullback` / dependent body 1 | direct M1 source-context group | 15228 aggregate | quick | 224,460 | 3,603.948 ms | generic helper broad | S partition, P ownership |

The last three rows partition direct cost and cannot be summed with the selected inclusive subtree times. The source key identifies the nearest prefix head, not the declaration that created the mismatch. The two pullback definitions are exact path nodes; neither is proven to be the original producer by reduction frequency.

## D. Root-to-source chain (§4.3)

Direct generated-field construction (S0, S) -> stored `_proof_2` `homMk`/`id` dependent pair (S4, S; S2 U). A separate measured chain is selected root 15228 dependent `Eq` M0 -> quick dependent-body and `homMk`/composition application argument 2 (S) -> `Algebra.Hom`/composition and induced-Hom projection paths (S) -> 23,288.322 ms M1, 12,479.586 ms M2, 2,528.957 ms Matched direct-exclusive time in that root (D measurement) -> `IsoAlgebra.liftOfStr` construction boundary avoids direct generated-law checks (S API-level counterfactual). The join from the stored `_proof_2` pair to root 15228 is unverified (U). Separately, two `Quiver.Hom` roots enter `Endofunctor.Algebra.a`/`FullSubcategory.proj` and then the exact `WeilSheaf.frobeniusPullback`/`ProEtaleWeilSheaf.frobeniusPowPullback` pair (S); their relation to individual stored proof constants also lacks a caller tag (U).

The type-correct same-declared-functor source control replaces direct fields with `IsoAlgebra.liftOfStr`; the aligned run emitted no root above 100 ms and whole-prefix CPU fell from 107.63 s to 9.38 s. Restoring direct fields returns the slow checks. This changes the whole construction and removes generated law roots, so it is an API-level one-factor construction control, not an M0-preserving one-field intervention. The earlier descendant-alignment control preserved the outer 10.9M-call root and did not reduce M2; it is a negative control for a single leaf. `liftOfStr` is fragile but effective: direct generated-field reconstruction punctures it. Its own regular hint does not prove that the head remains closed in every later use.

## E. Summary (§4.4)

| Case | Mismatch producer | Expansion gateway | Cost amplifier | Best valid control and effect | Overall evidence |
| --- | --- | --- | --- | --- | --- |
| PR1627 | direct `IsoAlgebra.mk`/`ObjectProperty.homMk` generated-field API (S) | dependent proof proposition and `homMk`/composition application (S) | `Algebra.Hom`, `FullSubcategory.proj`, `InducedCategory.Hom.proj`, and concrete pullback functor paths (S traversal, P field ownership) | `liftOfStr`, same declared functor but changed law roots: 107.63 -> 9.38 s whole-prefix CPU; restored direct fields slow | S for API boundary; U for finalization and field-to-root map |

To finish exact three-field attribution, instrument Kernel `check`/`isDefEq` entry with the generated declaration and field index, then attach that tag to MDA roots and add per-label exclusive counters to selected subtree records. This is needed because root serials are process-local and the current probe emits no caller tag. A matched pre-finalization law Expr is also needed before finalization can be assigned a causal role. All stored reduced files are below 5 MB.

## Audit note

The direct generated-field API, dependent gateway, and selected amplifier paths are **S**. `liftOfStr` is a broad construction counterfactual with restoration; the field-to-root join is **U**, so no individual proof field is D.
