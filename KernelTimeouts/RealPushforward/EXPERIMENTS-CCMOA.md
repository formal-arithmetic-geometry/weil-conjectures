# CCMOA: RealPushforward

Case `RealPushforward`; conversion `RP-final-exact-v1`; Lean 4.35.0 and the
case's pinned Mathlib revision. The root is the final `exact this` conversion
after the polynomial rewrites in `isReal_higherLowerShriek_one`.

## A: stages and first divergence

| Stage | Observation |
|---|---|
| S0 Source | The proof rewrites `FrobeniusModule.localPolynomial` and then passes `this` to the declared realness equality. The inferred equality is built from the concrete `frobeniusEnd.charpolyRev`; the declaration retains the local-polynomial vocabulary. |
| S1 Macro-expanded syntax | Rewriting and notation expansion preserve the same `Eq`/`Polynomial.coeff` spine. No macro-generated projection or dependent binder is the first difference. |
| S2 Elaborated Expr | Fresh snapshot roots: actual hash `2476657511`, expected hash `273099248`. Both are `Eq` over `Complex` with the same coercion and `Polynomial.coeff` heads. The first unequal polynomial argument is actual `LinearMap.charpolyRev ...` versus expected `FrobeniusModule.localPolynomial ...`; the exact expected constant node is recorded in `ccmoa/s2-snapshot.txt`. |
| S3 Declaration finalization | The imported declaration has no available pre-finalization term. No generated declaration is implicated. |
| S4 Stored environment | `LinearMap.charpolyRev` is regular height 26; `FrobeniusModule.localPolynomial` is regular height 27. Both are imported regular definitions. The remaining aligned pair has a smaller `Semifield.toCommSemiring` versus `CommRing.toCommSemiring` instance leaf. |
| S5 Kernel root pair | The original READY4.2 root is comparison-dominated: 17,340,236 calls, 12,362,803 failures/stuck, max depth 91, 143,714.229 ms comparison-exclusive and 96.269 ms reduction-exclusive. The deterministic release probe times out at about 55 s. |
| S6 Kernel exposure | The different polynomial heads force reduction into concrete stalk/module and `ContinuousMap`/`DFunLike.coe` descendants. The existing trace records the deep comparison path, but not a unique downstream semantic culprit. |

The first divergence is source/API-authored at S0/S1 and remains explicit at
S2. It is active at the `Polynomial.coeff` argument; no dependent helper
domain is involved.

## B: reused polynomial alignment

| Variant | Expr change | Obligation and result | READY4.2 counters |
|---|---|---|---|
| Original `FinalExact` | `Polynomial.coeff` receives `LinearMap.charpolyRev ...` on the inferred side and `FrobeniusModule.localPolynomial ...` on the goal side. | Same final `exact this` consumer; deterministic Kernel timeout. | 17,340,236 calls; 143,714.229 ms comparison; 96.269 ms reduction; max depth 91. |
| Polynomial-aligned `aligned-AlignedGoal` | Changes only the declared polynomial representation to `charpolyRev`, retaining the same realness proposition and final consumer. `AlignedHead` confirms the polynomial-head divergence is gone; the remaining first difference is the semiring-instance leaf. | Type-correct definitional alignment; the final obligation is preserved. | Largest root 35.158 ms / 2,873 calls; 13.648 ms comparison; 21.510 ms reduction; max depth 192. |
| Restoration `BeforeFinalSorry` | Keeps the original `localPolynomial` rewrite path and discards only the final consumer with `sorry`; it is a phase control, not a B control. | Confirms the prefix is cheap and the final conversion carries the root. | Prefix roots are below the expensive threshold; original root is restored by `FinalExact`. |

The aligned control changes the actual elaborated polynomial expression and
retains the same root equality. The large-to-shallow counter change is
therefore a valid one-factor representation control. The remaining semiring
instance mismatch is explicitly not claimed as causal for the original
timeout.

## C and D

C is not indicated. The first divergence is already present in source and
S2, and no instance or implicit assignment is the first unequal child. The
aligned head's remaining instance leaf is a negative control, not evidence of
an Elaborator-selected origin.

D is unobservable for the imported declaration. No S2/S4 difference or
generated proof field is implicated at the first divergent path.

## E: cheap-but-fragile boundaries

| Boundary | Current reason it is cheap/effective | Puncture and status |
|---|---|---|
| Polynomial representation alignment | Both sides use `charpolyRev`, so Kernel does not have to unfold `localPolynomial` into the concrete stalk/module path at this root. | Reintroducing the rewrite-produced `localPolynomial` head restores the timeout. **Fragile but effective.** |
| Abstract polynomial identity behind the fixed theorem | The fixed theorem checks the same proposition through a generic identity, avoiding the concrete final conversion. | Replacing it with direct `exact this` after the concrete rewrite punctures the boundary. **Fragile but effective.** |
| Semiring-instance leaf | The aligned pair still has `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`, yet remains shallow. | Treating this leaf as the primary cause is disproved by the aligned workload. **Not actually responsible for the original root.** |

## Synthesis row

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
|---|---|---|---|---|---|---|---|
| RealPushforward | S0/S1 | Source/API polynomial representation (**Demonstrated**) | No relevant first-stage choice observed (**Not observed**) | Pre-finalization comparison unavailable (**Unknown**) | Regular-head reduction into the concrete polynomial/stalk path (**Demonstrated**) | `charpolyRev`/polynomial-head alignment (**Demonstrated**) | Fragile but effective; direct concrete rewrites can puncture it (**Demonstrated**) |

The representation trigger is demonstrated by the exact S2 snapshot and the
same-consumer aligned control. The exact downstream `ContinuousMap` and
`DFunLike.coe` comparison amplifier remains **Plausible**, because the
available trace is path-level and not a semantic exclusive attribution.

## Audit note and Batch 2

The original and aligned proofs keep the same final `exact this` consumer and
change the declared polynomial head on the two equality sides. Unlike a
`type_of%` goal, the aligned goal still has a distinct semiring-instance
child. The saved S2 head audits and READY4.2 counters therefore support the
one-representation control; the remaining instance leaf is a negative
control. The frozen local replay uses the same source prefixes and records
the original/aligned Expr hashes and timings in `ccmoa/frozen-results.txt`.
Restoring the original local-polynomial goal punctures this cheap boundary.
The imported pre-finalization term is unavailable, so finalization is Unknown.
