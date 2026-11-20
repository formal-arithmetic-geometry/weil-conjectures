# STRUCTURE EXPOSURE AUDIT

Case: `RealPushforward`
Source snapshot: `ed3d39ddb5d`, `isReal_higherLowerShriek_one`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The cost is the final inferred-type/declared-type conversion at `exact this`,
after the two polynomial rewrites. The stored proposition has a coefficient
whose polynomial argument is
`LinearMap.charpolyRev (stalk ((higherLowerShriek ... 1).obj K) ξ)`; the
declared goal uses `FrobeniusModule.localPolynomial M`. The first material
mismatch is this single polynomial head (regular definitions of heights 26 and
27), with the same mismatch carried by the dependent stalk/module arguments.
This is a data-valued equality proposition, not a proof-body comparison.

Baseline `FinalExact`: 54.54 s wall and deterministic Kernel timeout (about
4.69 GB RSS). The type-only and prefix-with-`sorry` probes take 2.8--3.0 s.

## R2. Candidate exposure boundary

The outer `Polynomial.coeff` heads match. One source-level reduction of
`FrobeniusModule.localPolynomial M` exposes `M.frobeniusEnd.charpolyRev`; one
reduction of `LinearMap.charpolyRev` exposes `f.charpoly.reverse`. This is the
candidate boundary. The height-based unfolding order is a source-guided
prediction; no internal Kernel trace is claimed. `Expr.proj` is not on the
first divergent path.

## R3. Exposed data-bearing structure

```text
coefficient equality
|- Polynomial.coeff / Polynomial.reverse
|  |- LinearMap.charpolyRev versus FrobeniusModule.localPolynomial
|  |- stalk ((higherLowerShriek ...).obj K) and finite-point data
|  `- FrobeniusModule.frobeniusEnd and module representation
`- concrete semiring and PadicAlgCl instance arguments
```

The polynomial and stalk/module terms are directly visible in the preserved
`pp.explicit` pair. Their connection to the timeout beyond the first head is
structurally inferred.

## R4. Cost distribution and reduction footprint

The declared type and prefix are cheap; the final conversion is dominant:
54.54 s versus about 3 s. The aligned probe still reports a smaller
`Semifield.toCommSemiring`/`CommRing.toCommSemiring` leaf, but completes in
3.00 s (2.00 + 0.93 s CPU, about 3.13 GB RSS). Diagnostics on the original
conversion show deep reduction chains before timeout; exact per-child Kernel
times and a counter-to-child attribution are unavailable.

## R5. Causal control

`AlignedGoal.lean` changes only the definitionally equal declared polynomial
representation to `charpolyRev`, keeps the original consumer and obligation,
and is fully Kernel checked in 3.00 s. `AlignedHead.lean` verifies that the
polynomial mismatch moved to the smaller semiring-instance leaf. The remaining
leaf alone is therefore not sufficient. No restoration was needed for this
negative/control case; the immutable original probe is the restored mismatch.

## R6. Exposure-footprint comparison

Original: polynomial heads differ; the conversion enters the concrete
stalk/module polynomial representation and times out.
Aligned: polynomial heads are shared; only a small instance difference remains
and the same final conversion succeeds.
Restored: the original `FinalExact` pair and timeout return. The reduction
sequence is not observable, so the large downstream footprint is reported as
measured by the timeout/counters and structurally inferred as downstream.

## R7. Classification and confidence

Classification: **N (simple necessary unfolding)**.
Confidence: **Confirmed** for the necessary polynomial-head alignment;
**Plausible** for any particular downstream stalk/module amplifier.
Directly measured: exact final site, head pair, aligned successful control,
and timings. Structurally inferred: the one-step body and the data tree.
Unknown: the Kernel's internal reduction order and exact child attribution.

## Most important result

The small regular-head mismatch is sufficient to force the expensive initial
comparison, but the evidence does not establish a large nested exposure as the
primary mechanism. This is the required simple-unfolding control.
