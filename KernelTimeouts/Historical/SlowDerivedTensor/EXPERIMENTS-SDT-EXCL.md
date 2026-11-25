# Slow Derived Tensor: Other Factors Exclusion Report

## 1. Exact baseline and reproducibility

Stage I used the historical consumer `bdab171985a`, Mathlib
`0df444a360eaa60ab8c11cda51a86af692955474`, and Lean 4.33.1
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The executable and
loaded shared library were both READY4.2. Each process used one Lean worker
and a 3600 s timeout; experiment processes were sequential. The original
lemma value and declared type were not edited. The `M0` comparison was
`Kernel.isDefEq` on its Kernel-inferred and declared types. **Direct root
evidence.**

| Fresh comparison | Repetitions | Calls | Exclusive total, median (range) |
|---|---:|---:|---:|
| Exact `M0` | 3 | 6,239,533 each | 45.229 s (45.127-45.582) |
| Original source `F_L ≟ F_R` | 3 | 28,223 each | 0.155 s (0.155-0.159) |
| Extracted `U_L ≟ U_R` | 3 | 6,239,463 each | 45.878 s (45.831-50.206) |
| Extracted `map` | 3 | 1,902,433 each | 14.537 s (14.499-14.575) |
| Extracted `map_comp` | 3 | 4,196,948 each | 33.285 s (33.042-33.472) |

The exact `M0` median partitions into 25.675 s comparison-exclusive and
19.554 s reduction-exclusive time. The extracted `U` replay has 70 fewer
calls than `M0`; its field replays are separate calls and must not be added
to `M0` or `U`. The high end of the `U` range followed an `M0` replay
in the same process. End-of-process restored baselines below control this
ordering effect. Counters and comparison labels are in `sdtexcl/`.
**Direct root evidence; Direct child replay.**

## 2. Complete unequal-input inventory

The `Functor.comp` source expressions have the following relevant arguments.
The inventory comes from the fresh elaborated Expr probe, not printed source
syntax. **Direct child replay.**

| Location | Left/right exact representation | Status |
|---|---|---|
| `F.arg0..3` | Source `HomotopyCategory`, its category, source functor category and category instance | Structurally shared |
| `F.arg4` | `C ⥤ DerivedMonoidal Qh quasiIso_L/R` | Unequal hidden universe-instantiated `quasiIso` |
| `F.arg5` | `Functor.category` for `F.arg4` | Unequal through target type |
| `F.arg6` | `curriedTensor C` | Left uses `HomotopyCategory.MonoidalCategory.instMonoidalCategory`; right uses `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` |
| `F.arg7` | `(Functor.whiskeringRight C C (DerivedMonoidal Qh quasiIso_L/R)).obj (toDerivedMonoidal Qh quasiIso_L/R)` | Unequal target/wrapper and localization arguments |
| `F.arg7.arg5` | `toDerivedMonoidal Qh quasiIso_L/R` | `Qh` shared; `quasiIso` constant levels unequal |
| Outer derived-bifunctor arguments | `Qh` and `IsLocalization` provider | Structurally shared |
| Outer `ContainsIdentities` provider | Same theorem head, different `quasiIso` argument | Unequal; not an argument of `toDerivedMonoidal` itself |
| `uncurry` source/product category arguments | The two copies of `C`, their category instances, and product arguments | Structurally shared |
| `uncurry` target and source-functor arguments | Target type/category and `F` | Unequal as above |

The first exact structural leaf is
`HomotopyCategory.quasiIso.{succ u, max (succ u) u', 0}` versus
`HomotopyCategory.quasiIso.{succ u, max (max u' (succ u)) u, 0}`.
These universe expressions are accepted as definitionally equal in the
rebuilt terms, but the constants are not structurally identical. The
difference occurs in the instantiated `F` target type and survives in
`U.map` and `U.map_comp` expressions and types. The first operational
source divergence is the `curriedTensor` instance. **Direct child replay;
Inference for universe normalization.**

## 3. Prior controls reused

Round 5's target-type, target-category, and wrapper substitutions retained
the expensive uncurried path, while aligning only the `curriedTensor`
instance made `F`, `U`, and fields millisecond-scale. The present run
replayed those arguments once with READY4.2 counters and repeated instance
alignment in all three matrix processes. These are API-level rebuilt Exprs,
not M0-preserving local cuts. **API-level counterfactual.**

## 4. New valid one-factor controls

All reported candidates passed `checkWithKernel` as source and uncurried
terms and returned `true` in the four comparisons. Each kept the original
lemma and `M0` snapshot untouched; only E0 preserves the exact original
root obligation. The counterfactuals preserve the mathematical statement
but rebuild an API-level source term. **API-level counterfactual.**

| ID | Changed argument | Fresh `U` calls; exclusive time | Result |
|---|---|---|---|
| E0 | None | 6,239,463; median 45.878 s | Original expensive path |
| E1 | `F.arg6` source monoidal instance aligned | No root over 100 ms; 4 ms wall in each run | Path removed |
| E2 | Right `quasiIso` universe constant aligned in `F.arg4,5,7`; source instance retained | 6,239,463; median 51.195 s (50.902-51.314) | Same calls and paired time as restored E0 |
| E3 | Entire right `F.arg7.arg5` localization functor aligned | 6,239,463; median 51.140 s (50.728-51.283) | Same expensive path; broader argument replacement |
| E3W | Only the right `quasiIso` constant inside `toDerivedMonoidal` aligned | 6,239,463; 50.826 s | Same expensive path; strict localization-argument check |
| E4 | `F.arg5` target category instance aligned | 6,239,463; 50.273 s | Same expensive path |
| E5 | `F.arg4` target type aligned | 6,239,463; 50.235 s | Same expensive path |
| E6 | `F.arg7` entire whiskering argument aligned | 6,239,463; 50.734 s | Same expensive path |
| E7 | Source/product category instance | No unequal argument found | Not applicable |
| E8 | Non-instance declaration hint | No unequal hint for a common reached declaration | No valid isolated metadata control |

E2 aligns one logical factor across all three occurrences; the before and
after constants are the two universe instantiations in section 2. E3 aligns
one argument expression but bundles its hidden target representation, so
E3W is the stricter B control. E4-E6 replace one `Functor.comp` argument
each. E1, E4-E6 have prior negative/positive controls; E2, E3, and E3W
are new. `F` costs were about 0.16 s for all expensive rows, versus 1 ms
for E1. All expensive rows entered both morphism fields. The first-branch
path for E2/E3 was not separately traced; identical field entry and call
counts are direct evidence, while branch identity remains **Unknown**.

## 5. `quasiIso` and universe result

E2 is a valid same-typed provider-only alignment with the source instance
mismatch retained. It changes the right constant's universe instantiation
everywhere it occurs in `F.arg4,5,7`, passes Kernel type checking, and
retains exactly 6,239,463 `U`, 1,902,433 `map`, and 4,196,948
`map_comp` calls in all three runs. In the two paired runs, E2 `U`
exclusive time differs from restored E0 by -0.079 s and +0.126 s, both
below 0.3%. Thus its structural survival is observed, but no independent
material cost is demonstrated. **Direct child replay; API-level
counterfactual.**

## 6. Localization and `toDerivedMonoidal` result

`Qh` is pointer-shared, and `toDerivedMonoidal L W` is definitionally
`L`. Its term has six arguments; no separate `IsLocalization` or
`ContainsIdentities` proof is passed to this definition. Its unequal
argument is the universe-instantiated `W = quasiIso`; the outer
derived-bifunctor does carry the shared localization proof and an unequal
`ContainsIdentities` theorem application. E3 and the narrower E3W
both retained the full `U`, `map`, and `map_comp` call counts. E3W
was 50.826 s against a 51.207 s restored E0 in the same process.
No separate localization-functor producer is demonstrated. **Direct child
replay; API-level counterfactual.**

## 7. Target category and wrapper controls

The target `DerivedMonoidal` type and its category instance contain unequal
hidden `quasiIso` parameters; target Hom and `CategoryStruct.comp`
expressions therefore have unequal representations. E4 and E5 each kept
6,239,463 `U` calls and both expensive fields. E6 did likewise. These
controls exclude an independent producer at this argument boundary, while
the prior same-root trace still shows target Hom/composition as the context
that carries source-instance differences into `map` and `map_comp`.
The latter is a cost-context inference, not a newly isolated target
amplification estimate. **API-level counterfactual; Direct child replay
(prior trace); Inference.**

## 8. Reducibility and Kernel hint audit

Fresh environment queries recorded exact `ReducibilityHints`:

| Reached declarations | Kind and hint |
|---|---|
| `Functor.comp`; `Functor.category` | def, regular(1); def, regular(2) |
| `curriedTensor`; `Functor.uncurry`; `instCategoryDerivedMonoidal` | def, regular(3) each |
| `Functor.whiskeringRight`; `DerivedMonoidal`; `toDerivedMonoidal` | def, regular(4); def, regular(2); def, regular(2) |
| `HomotopyCategory.quasiIso`; `DerivedCategory.Qh` | def, regular(16); def, regular(15) |
| `Functor.obj`, `Functor.map`, `NatTrans.app`, `CategoryStruct.comp` | def, abbrev each |
| `tensorObj`, `whiskerLeft`, `whiskerRight` projections | def, abbrev each |
| `Functor.mk` | constructor |
| Left and right source monoidal providers | def, regular(24); def, regular(25) |
| `IsLocalization` and `ContainsIdentities` providers | theorem each |

The prior parent-child trace records lazy-delta entering `Functor.obj`
and exposing `Functor.mk`, and paired `Functor.map`/`NatTrans.app`
unfolding to `whiskerLeft`/`whiskerRight`; it does not justify charging
the entire root to any one delta head. The two provider hints differ, but
that is part of the instance factor reserved for Stage II. No common
non-instance declaration has a left/right hint mismatch. Changing hints
would change the pinned declaration environment, so E8 was not run.
No Kernel semantics were changed. **Direct child replay (prior trace);
Direct environment audit; Unknown for a hypothetical E8 intervention.**

## 9. Interaction controls

The §4 gate found no reproducible material non-instance effect. Therefore
the conditional I00/I10/I01/I11 factorial matrix was not triggered.
E0, E1, and E2 already provide the I00, I10, and provider-aligned I01
observations at the API level; I11 was not needed for causal attribution.
**Inference from direct counterfactual measurements.**

## 10. Per-field cost changes

These are independent direct field replays, not same-root shares:

| Variant | `F` calls; median time | `U` calls; median time | `map` calls; median time | `map_comp` calls; median time |
|---|---|---|---|---|
| E0 | 28,223; 0.155 s | 6,239,463; 45.878 s | 1,902,433; 14.537 s | 4,196,948; 33.285 s |
| E1 | below threshold; 1 ms | below threshold; 4 ms | below threshold; 1 ms | below threshold; 3 ms |
| E2 | 28,223; 0.161 s | 6,239,463; 51.195 s | 1,902,433; 14.586 s | 4,196,948; 33.563 s |
| E3 | 28,217; 0.162 s | 6,239,463; 51.140 s | 1,902,433; 14.662 s | 4,196,948; 33.557 s |

For E2, `map` ranged 14.539-14.720 s and `map_comp` 33.517-33.761 s.
For E3, the ranges were 14.632-14.783 s and 33.320-33.737 s.
E3's six-call `F` difference is 0.02% and does not propagate to `U`.
Restored E0 `U` was 51.393 s and 51.069 s in the paired runs; the
corresponding E2 values were 51.314 s and 51.195 s, and E3 values
51.283 s and 50.728 s. Thus the unpaired median rise is run-order
drift. **Direct child replay.**

## 11. Immediate conclusion

**Instance-only producer supported among the tested factors.** No tested
non-instance difference reproducibly changed the expensive call path or
exclusive time beyond paired run noise. Aligning the `curriedTensor`
monoidal instance alone removed the path. The §4 gate verdict is **no
reproducible material non-instance effect found**. This does not mean the
target Hom/composition context is free; it is where the source difference
is compared. The two-instance provenance question remains interpretable
for a separate Stage II run. **Direct root evidence; API-level
counterfactual; Inference for producer attribution.**

## 12. Remaining unresolved factors and data

The exact first branch for each new control and a type-preserving
alternative target representation were not independently traced.
Individual monoidal-field and proof-law causality belongs to Stage II.
E3W has one instrumented repetition because it showed unchanged calls
and a below-1% paired time difference; the broader E3 and E2 each have
three. These limits do not change the §4 gate. **Unknown.**

Reduced probes, fresh comparison logs, root counters, Expr inventory,
and hint audit are in `sdtexcl/`. All reduced files are below 5 MB,
contain no machine paths or host identifiers, and no raw trace was
placed in the repository. Disk usage remained 84%. No commit or
push was made.
