# CCMOA: PR1627 Weil-sheaf transport

Scope: the historical direct `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor` construction, Lean 4.35.0. This report reuses `EXPERIMENTS-MOE.md`, `EXPERIMENTS-M1P.md`, `ANATOMY.md`, and their raw probes. The exact pre-finalization law value was not captured by the previous audit.

## A. Stages and first divergence

| Stage | Snapshot and result |
| --- | --- |
| S0 | Original `powFunctor` writes `IsoAlgebra.mk` for `obj` and `ObjectProperty.homMk` for `map`; the fast variant writes `IsoAlgebra.liftOfStr`. These are different source API constructions. |
| S1 | The relevant direct field applications are ordinary structure/application syntax; no macro-originated head change was observed. |
| S2 | The prior `moe/source-generated.snapshot` records only an unrelated identity lambda at S2. A new source-local `#moe_elab` attempt in `ccmoa/PreFinalizationAttempt.lean` did not finish after 15 minutes and was stopped; it produced no S2 law Expr. Thus the exact generated-law pair is **unobservable** at S2 in this audit. |
| S3 | Declaration processing generated opaque `powFunctor._proof_1`, `_proof_2`, and `_proof_3`. The stored `_proof_2` type has nine binders and value eight. This does not locate when the divergent dependent domain arose. |
| S4 | `moe/source-generated.snapshot` and the source-local prefix audit inspect the actual stored values. `powFunctor` is `regular:59`; `frobeniusPowPullback` is `abbrev`; `CategoryStruct.id` is `abbrev`; each `_proof_*` theorem is `opaque`; `liftOfStr` is `regular:6`. |
| S5 | In `_proof_2`, the checked type of application argument 1 is compared with the domain of the **already applied prefix**, after argument 0 has been instantiated. `Kernel.isDefEq` returns true for this structurally different pair. This is not a comparison with the generic `id` binder. |
| S6 | READY4.2 root 15228 has 10,904,899 calls, depth 61: M1 2,619,482, M2 1,512,663, Matched 6,772,753. M1 application and dependent-body descent propagate the difference; reduction exposes further descendants. |

The exact first stored unequal node for `_proof_2` argument 1 is `root/body/arg/fn/fn/fn`: actual `@ObjectProperty.homMk (Endofunctor.Algebra (frobeniusPowPullback k₀ l Y r)) (Algebra.instCategory ...) (Algebra.IsIsoStr ...)`; expected `@CategoryStruct.id`. The `id` proof argument is an application of a function to a dependent proposition and a lambda. Its first argument is instantiated before deriving the lambda's expected domain. The corresponding checked argument in `_proof_3` is structurally aligned. The earliest **verified exact pair** is S4; the direct `homMk` API choice is visible at S0, but the S2-to-S4 timing of this paired law obligation is Unknown. This is an active dependent-argument comparison, with additional Kernel-exposed M1/M2 descendants.

## B. Controls and READY4.2 workload

| Control | Elaborated/stored Expr change and obligation | Counters |
| --- | --- | --- |
| Direct generated fields (original/restored) | Direct `IsoAlgebra.mk`/`ObjectProperty.homMk`; same declared `powFunctor` type and generated-field checks. | Largest READY4.2 root: 10,904,899 calls; M1 2,619,482; M2 1,512,663. Separate generated-field roots include 4,696,766 calls. |
| Generic `liftOfStr` | Value head changes to `IsoAlgebra.liftOfStr`; same declared functor type, but the generated law-field root disappears. This is a **construction-boundary diagnostic**, not a one-field control preserving the original root. | Aligned counters contain no root above the 100 ms threshold; exact subthreshold calls were not recorded. |
| `MatchedGeneric` | Same-provider generated-field versus `id`-wrapped field; both kernel-check, but it changes the consumer/telescope. | One call, 0.009 ms in the earlier zero-threshold instrumented diagnostic; not a READY4.2 paired field count. |

The direct/generic source change is type-correct and reversible; the restored direct construction returns to the slow root. It changes the entire construction, so it cannot establish a causal effect for any single generated field. No valid one-factor replacement of just the `_proof_2` dependent domain preserving the original telescope was available. The three generated obligations must not be treated as one identical root: `_proof_1` has a nonstructural `CategoryStruct.id` argument type, `_proof_2` has the exact `homMk`/`id` divergence, and `_proof_3` argument 1 is structurally equal.

## C and D. Provenance and finalization

The stored `homMk` Expr contains explicit `Algebra.instCategory (frobeniusPowPullback ...)` and `Algebra.IsIsoStr (frobeniusPowPullback ...)` arguments. No competing provider, coercion, or Meta transparency decision was isolated as the first divergent child. The source head `homMk` is already written; elaboration fills its implicit arguments. No fresh-state assignment perturbation with a changed final Expr and matched Kernel replay exists, so Elaborator causality is **Not observed**.

The three generated theorem constants and their opaque hints are observed after finalization. The nine/eight binder asymmetry in `_proof_2` is real stored metadata, but an imported constant exposes no pre-finalization Expr. The scratch source-local attempt failed to yield an S2 law snapshot. Therefore the claim that `abstractNestedProofs` or finalization *created* the `homMk`/`id` mismatch is **Unknown**. Opacity does not make the dependent proposition type comparison cheap when the proof-containing data is checked.

## E. Boundary inventory

| Boundary | Why cheap now, puncture, status |
| --- | --- |
| `IsoAlgebra.liftOfStr`, `regular:6` | Generic helper keeps the use site at a named head and avoids the three direct generated-field checks. Replacing it with direct fields restores the 10,904,899-call root. **Fragile but effective**; inlining or downstream direct reconstruction can puncture it. |
| `frobeniusPowPullback`, `abbrev` | Compact named domain, but its body is reducible during dependent comparison. Unfolding/substituting the raw Frobenius functor was not isolated. **Untested** as a protective boundary. |
| Generated `_proof_1`-`_proof_3`, `opaque` | Opaque values hide proof bodies after storage; the relevant proposition types still carry the direct construction. A proof-only replacement preserving the full telescope was not found. **Fragile but effective** for body exposure, not established as the cause of the original root. |

## Synthesis

| Case | Earliest divergence stage | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| PR1627 | S4 exact pair; S0 direct API choice (**Plausible** timing) | Direct generated-field API (**Strongly supported**) | **Not observed** | **Unknown** | **Strongly supported** M1/M2 descendants | Generic `liftOfStr` (**Strongly supported**) | **Strongly supported** fragile |

The `Demonstrated` level is withheld: the generic helper changes the generated root, and no valid one-field control changes the exact divergence and READY4.2 workload while preserving that root.

## Audit note and Batch 2

The generated proof fields trigger the conditional finalization audit, but
`ccmoa/PreFinalizationAttempt.lean` yielded no S2 law Expr before its bounded
stop. The stored nine/eight-binder asymmetry is an S4 fact, not evidence that
finalization created the `homMk`/`id` split. The direct/generic restoration
punctures the construction boundary, while changing the whole generated law
root; no one-field puncture is available. No selected transparency constraint
with a changed final Expr was identified.
