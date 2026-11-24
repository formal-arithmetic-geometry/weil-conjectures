# Mismatch-to-definition attribution: OrderedSpectralRawLattices

Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; source snapshot `f4946fdb6b68a7010f913438a6d4e3c22ee59025`; measurement import revision `105ac3f5b23c1e6eefcf6fd1fd3f8ce745df071d`. Probe: `probes/mprwe/Original.lean` (SHA-256 `b4a034e76751a5aead274e23ad53bdc8fe4b637e5bb5f65648380d90a66ccbc7`). Root `62844` is the final inferred-helper-type versus declared-`RawStratifiedLattices` conversion in `AlgebraicGeometry.ProEtale.small_spectral_raw_lattices`. Its exact structural Expr pair, including universes and implicit arguments, is `mda/pairs-1.jsonl.gz`, call 1; the local context and source site are in `probes/HeadAudit.lean` and `EXPERIMENTS-MOE.md`.

The fresh MDA trace has 18,944,709 calls, 99,604.149 ms comparison-exclusive and 24.978 ms reduction-exclusive time, maximum depth 71, and the expected deterministic Kernel timeout. M1: 8,320,909 calls / 65,599.012 ms; M2: 3,499,646 / 32,385.184 ms; Matched: 7,124,151 / 559.398 ms; M0: one call / 91.929 ms; Unclassified: two calls / 968.625 ms. The established READY4.2 topology for this same 18,944,709-call root gives M1 median depth 64, mean fan-out 1.754, and maximum fan-out 18. The checked field-aware groups, labels, transitions, and root coverage reconcile in `mda/validation.md` and `mda/analysis.txt`. These trace timings include instrumentation overhead and are not substituted for the existing release/control timings.

## 4.1 Gateway-to-cost

| Gateway ID | Parent M0 path | Kernel branch and exact child pair | Source/API candidate | M1 calls | M1 exclusive time | Evidence |
| --- | --- | --- | --- | ---: | ---: | --- |
| `62844:2` | `root/binder_body[17]` | `quick/dependent-body[17]`; exact `8`/`8` Expr in `mda/pairs-1.jsonl.gz` | Instantiated lattice predicate below `RawStratifiedLattices` | 8,320,909 in its subtree | 65,599.012 ms in its subtree | S for entry; no local causal cut |
| `62844:5028` | call 2 | `quick/dependent-body[2]`; exact `Exists`/`Exists` pair in `mda/pairs-1.jsonl.gz` | Dependent existential lattice obligation | 8,319,002 in its subtree | Not exported per inclusive subtree | S for path, U for isolated time |
| `62844:9853` | calls 5031, 5032, 5033, 8203, 8205, 9851 | `application/argument[0]`; exact `Quiver.Hom`/`Quiver.Hom` in `mda/pairs-3.jsonl.gz` | Morphism domain under the lattice predicate | 8,317,216 in its subtree | Not exported per inclusive subtree | S for path, U for isolated time |
| `62844:9865` | `Quiver.Hom` -> `Mod.Hom` | `application/argument[9]`; exact `Functor.obj`/`Functor.obj` in `mda/pairs-4.jsonl.gz`; delta records `Mod.mk`/`Mod.mk` | Module object and functor component | 8,317,213 in its subtree | Not exported per inclusive subtree | S for path, P as amplifier owner |

These selected inclusive rows nest. Call 2 contains all measured M1 cost and is assigned that cost once. The complete direct, non-overlapping M1 partition in `mda/core.jsonl.gz` identifies the following largest gateway/component groups; the source label is the nearest source head, not proof that it produced M0:

| Gateway/component/source path | M1 calls | Direct M1 exclusive ms |
| --- | ---: | ---: |
| `projection/projection[0]` / `ProEtale.toSpecZ` | 3,623,811 | 18,760.864 |
| `application/argument[0]` / `ProEtale.toSpecZ` | 1,058,814 | 15,704.319 |
| `quick/dependent-body[1]` / `ProEtale.toSpecZ` | 483,172 | 15,157.284 |
| `application/argument[2]` / `ProEtale.toSpecZ` | 363,844 | 3,981.849 |
| `application/argument[4]` / `ProEtale.toSpecZ` | 268,430 | 3,535.369 |
| `application/argument[5]` / `ProEtale.toSpecZ` | 724,759 | 3,116.261 |

The selected top-12 pairs follow the long first spine and do not include a representative of every high-cost `toSpecZ` group. The tool's group key also drops the full ancestor Expr path. Consequently the exact `toSpecZ` field major premise and a non-overlapping R/H/D provider-by-provider split are **U**. That measurement needs a path-preserving group key or bounded representatives for each group plus provider-argument ancestry, rather than another unfolding-frequency count. `projection[0]` is an index, not a confidently resolved field name for `toSpecZ`.

## 4.2 Definition/API path

| Candidate definition/API | Role | First seen | Kernel path | M1 calls / exclusive ms | Intervention | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| Local R/H/D availability versus imported helper providers | Mismatch producer bundle | S0 availability, concrete S2 terms | Both `continuousMapRingObj` let values | No isolated share | All-route alignment succeeds; each route restoration reopens cost | S bundle; P individual route |
| `Semifield.toCommSemiring` / `CommRing.toCommSemiring` | First observed provider divergence | S2, first let topology argument | `spectralNorm.nontriviallyNormedField` -> `IsLocalRing.toNontrivial` | Not separately timed | R/H removal moves mismatch to domain route | S divergence; P cost role |
| `IsDomain.of_isSimpleRing` versus `instIsDomain` | Alternative provider divergence after R/H removal | S2 control | `Algebra.IsSeparable.of_integral` | Not separately timed | R/H-only control still times out | S divergence; P cost role |
| Dependent `RawStratifiedLattices` / `Exists` body | Expansion gateway | call 2 / call 5028 | `quick/dependent-body` | 8,320,909 / 65,599.012 in call-2 subtree | All-route alignment changes M0 | S |
| `Quiver.Hom` -> `CategoryTheory.Mod.Hom` -> `Functor.obj` | Downstream amplifier path | calls 9853-9865 | application, WHNF, application | 8,317,213 M1 calls inside call 9865; isolated M1 time U | No valid M0-preserving local control | S path; P ownership |
| `ProEtale.toSpecZ` nearest-source groups | Downstream component path | MDA direct groups | projection, application, dependent body | 5,165,797 calls / 49,622.468 ms across three largest disjoint groups | No local control | S direct accounting; P declaration causality |

The source-authored route availability and the Elaborator's S2 choice are distinct. The imported helper's provider terms are fixed by its stored type. Existing MOE snapshots show the first full-root leaf as `Semifield.toCommSemiring` versus `CommRing.toCommSemiring` in both ring-object values; the R/H-disabled control exposes `instIsDomain` versus `IsDomain.of_isSimpleRing`. They do not isolate the Kernel cost of each provider.

## 4.3 Root-to-source chain

Local R/H/D instance availability plus a previously elaborated helper type -> two different concrete provider paths in the two `Profinite.continuousMapRingObj` values -> S2 semiring M0 beneath the topology/spectral-norm instance -> call `62844:2` dependent lattice body, then call `5028` `Exists` -> calls `9853-9865` `Quiver.Hom`, `Mod.Hom`, and `Functor.obj` -> repeated projection, application, and dependent-body M1 work (65,599.012 ms total, with the six direct groups above covering 60,255.946 ms) -> all three route-availability changes align both ring values and the checked declaration succeeds. The link from the provider bundle to the full subtree is supported by the control matrix; individual provider-to-field shares remain unmeasured.

## 4.4 Summary and boundary

| Mismatch producer | Expansion gateway | Cost amplifier | Best valid intervention and effect | Evidence |
| --- | --- | --- | --- | --- |
| R/H/D provider bundle chosen at S2 against imported fixed terms | Dependent `RawStratifiedLattices`/`Exists` body at call 2 | `Quiver.Hom`/`Mod.Hom`/`Functor.obj`, then `toSpecZ` projection/application/body direct groups | Best one-factor puncture: restore D from the all-aligned control, returning a 18,944,728-call timeout. No successful one-factor fix. The three-route alignment succeeds in 10.11 s. | Producer S; gateway S; amplifier S for measured path, P for exact provider-field ownership; one-factor puncture S, bundle control S |

No successful **single-route** intervention exists: disabling R, H, or D alone retains the first mismatch; R/H removal moves it to the domain route; the all-route control changes M0. Its three availability changes are a bundle-level API counterfactual, not a one-factor or M0-preserving descendant cut. The existing one-route restorations are one-factor punctures of the aligned boundary and return the expensive path. `continuousMapRingObj` has an `abbrev` hint; the aligned two ring values are structurally equal, so the current boundary is fragile but effective. The named regular `RawStratifiedLattices` wrapper alone did not cause the measured timeout. Future independent provider reconstruction can puncture the alignment.

Remaining uncertainty: the imported helper's pre-finalization Expr, the complete R/H/D provider bundle on both sides as separately tagged paths, each provider's first expensive field, and per-subtree M1-only exclusive time below call 2 are unavailable in this tool output. The selected top-12 rows follow one inclusive spine; a top-100 replay was stopped when another package process appeared and the shared two-Lean-process limit would have been exceeded. A provider-tagged ancestor path for every direct group, bounded representative exact pairs for high-cost groups, and M1-only subtree totals would resolve the provider/field split; an imported pre-finalization snapshot would be required for finalization attribution. No causal Elaborator-only or finalization claim is made.

## Audit note

The R/H/D bundle is **S** because all-route alignment and one-route
restorations change the expensive path, but no single route is sufficient.
The dependent body and `toSpecZ` path are **S** as selected traversal. Individual
provider fields and M1-only subtree ownership remain **U/P**; inclusive rows
cannot be summed into route-specific costs.
