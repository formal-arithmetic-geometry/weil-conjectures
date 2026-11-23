# CCMOA report: RealPurity

Case: `KernelTimeouts/RealPurity`  
Declaration: `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`  
Root: final `exact h` in `hreal' : W.IsReal l P.obj.rho iota`, after the two
polynomial rewrites. The measurements below reuse the existing AD/IM/M1P/
MPRWE probes and READY4.2 counters; no historical control was rerun.

## A. Stage snapshots

The source-level application is the local proof `hreal x n` followed by
rewrites from `FrobeniusModule.localPolynomial` and
`WeilGroup.localPolynomial`. The helper domain is therefore the actual
`W.IsReal l P.obj.rho iota` pointwise equality after all preceding arguments are
fixed; it is not a generic polynomial binder.

| Stage | Snapshot and result |
| --- | --- |
| S0 | Source writes the two polynomial APIs and supplies `h` directly to `exact`. The two API choices select different concrete coefficient-ring paths. The source spelling of the ring instance is implicit. |
| S1 | No notation or macro expansion changes the application. The saved head probes use the same ordinary term after macro expansion. |
| S2 | The actual and expected types both print as `starRingEnd Complex (iota (...).charpoly.reverse.coeff n) = iota (...).charpoly.reverse.coeff n`. Structural inspection under `Eq` -> coercion -> `Polynomial.coeff` -> `Polynomial.reverse` finds `Field.toCommRing` in `h` versus `AlgebraicClosure.instCommRing` in the goal, on both equality sides. The first exact ring leaf is thus an elaborated instance argument. |
| S3 | The local proof is in an imported source snapshot. No pre-finalization term for the theorem is available; finalization is observational-only. No generated auxiliary declaration is implicated at this root. |
| S4 | `Field.toCommRing` is an `abbrev` (universe 0); `AlgebraicClosure.instCommRing` is a regular definition (universe 0, height 29). The target theorem is opaque in the stored environment. These hints explain a possible exposure order but do not identify the costly child. |
| S5 | READY4.2 original root: 17,310,168 calls, depth 93, 53,567.848 ms comparison-exclusive, 7.315 ms reduction-exclusive, deterministic timeout. The exact root pair is `inferType h` versus the current goal. |
| S6 | Kernel reduction exposes the polynomial/coercion tree. After both ring leaves are changed to the `h` representation, the first remaining difference moves to `Functor.obj` versus local `P` under `LinearMap.charpoly`; the expensive `DFunLike.coe`/`ContinuousMap` family remains. READY3.2 attribution for the original is M1 7,988,264 calls / 63.672%, M2 4,357,093 / 35.139%, matched 4,964,810 / 1.189%. |

**First divergence.** The API boundary is visible at S0/S1; the first exact
structural leaf in the instantiated pair is S2. It is active when the Kernel
descends through `Polynomial.reverse`, not merely a pretty-print difference.
The ring provider is source/elaboration materialized; the later object tree is
Kernel-exposed. The exact downstream semantic child remains unresolved.

## B. One-factor representation controls

All controls keep the original `hreal'` consumer, local context, and theorem
obligation. The controls replace only the selected ring leaf using the actual
type of `h`, then restore the original source.

| Variant | Expr change | READY4.2 root result |
| --- | --- | --- |
| Original | `Field.toCommRing` vs `AlgebraicClosure.instCommRing` on both equality sides | 17,310,168 calls; 53,567.848 ms comparison; timeout |
| Left leaf | Left equality-side goal leaf replaced with the corresponding `Field.toCommRing` subtree | 17,310,167 calls; 53,374.125 ms comparison; timeout |
| Right leaf | Right equality-side leaf replaced; same construction as left, mirrored | Timeout-scale root; no reduction to the cheap prefix |
| Both leaves | Both goal leaves replaced by the corresponding actual subtrees; first difference moves to `Functor.obj`/`P` | 17,310,167 calls; 53,374.125 ms comparison; timeout |
| Restored | Original ring leaves restored | 17,310,167 calls; 55,234.632 ms comparison; timeout |

The one-factor edits do change the elaborated expression and preserve the
root obligation, but they do not change the workload materially. The checked
`PolynomialTransport` route is cheap (7.10 s for the local proof) and
`Master.lean` is 6.10 s, but both change proof construction and are not
one-factor controls. Therefore the ring leaf is a **negative control**, not a
causal explanation. Exact counter lines are in `ccmoa/counters.txt`.

## C. Targeted elaborator provenance

The relevant S2 arguments are the inferred commutative-ring structures. The
head audit identifies the two provider constants and their hints. No fresh
metavariable/transparency trial produced an alternative provider while
keeping the same local context, expected type, and consumer. The existing
left/right/both controls change the final Expr but retain the timeout; no
elaborator-only assignment change with a workload change was demonstrated.

Result: provider selection is **Plausible** as the first representation
origin, but an Elaborator causal contribution is **Not observed**. No D audit
is indicated: there is no S2-to-S3 generated-field change at the root, and the
imported pre-finalization term is unavailable.

## D. Cheap-but-fragile boundary inventory (E)

| Boundary | Current behavior | Puncture and risk | Status |
| --- | --- | --- | --- |
| `Eq` around polynomial equality | Matching `Eq`/coercion/reverse heads give a compact outer comparison until the ring leaf is unfolded. | Unfolding `Polynomial.reverse`, changing coefficient APIs, or reconstructing an independent ring instance exposes the provider split and the downstream object tree. | Fragile but effective |
| Whole local polynomial transport | `PolynomialTransport` compares a shared polynomial equality and avoids the original `exact h` conversion. | Replacing it with direct `exact h` restores the timeout-scale conversion. | Fragile but effective |
| Named regular ring heads | `Field.toCommRing` is an abbrev and `AlgebraicClosure.instCommRing` is regular height 29. | Changing declaration kind or inheritance order can alter Kernel exposure, but no causal timing is established here. | Untested |
| Frobenius/stalk object boundary | After ring alignment the `Functor.obj`/local-`P` pair remains expensive. | Inlining or changing the producer can expose proof-laden category data. | Untested |

## Synthesis row

| Case | Earliest divergence stage | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| RealPurity | S0/S1 API choice; exact ring leaf S2 (**Strongly supported**) | Instance representation under the two polynomial APIs (**Plausible**) | Not observed | Unknown | Strongly supported | Whole-polynomial transport / named polynomial boundary (**Strongly supported**) | Fragile but effective (**Plausible**) |

## Audit note and Batch 2

The earlier "Demonstrated as observations" wording was incompatible with
the strict causal definition. The same-obligation one-leaf controls change
the Expr but leave the 17.31M-call workload unchanged, so the ring leaf is a
negative causal control. The existing left, right, and both-leaf replays are
the triggered frozen comparisons; they already test distinct Exprs under the
same root. Restoring direct `exact h` punctures the whole-polynomial transport
boundary; no additional provider or transparency perturbation is justified.
